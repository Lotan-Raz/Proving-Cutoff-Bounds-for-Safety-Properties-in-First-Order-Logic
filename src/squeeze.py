from typing import Iterable, List, Optional, Dict, Tuple, Set, Generator, Iterator
import syntax
import solver
from itertools import combinations, chain
import logging
from dataclasses import dataclass

logger = logging.getLogger(__name__)

LOW = '_l'

def add_low_to_program() -> None:
    global LOWS
    global TRANSITIONS
    global IDLE

    TRANSITIONS = tuple(t.as_twostate_formula(syntax.the_program.scope) for t in syntax.the_program.transitions())
    IDLE = syntax.DefinitionDecl(True, 2, 'idle', (), (), syntax.TrueExpr).as_twostate_formula(syntax.the_program.scope)

    LOWS = {}
    new_decls = []
    for d in syntax.the_program.decls:
        match d:
            case syntax.RelationDecl():
                low_name = syntax.the_program.scope.fresh(d.name + LOW)
                d_low = syntax.RelationDecl(low_name, d.arity, d.mutable)
                new_decls.append(d_low)
                syntax.the_program.scope.add_relation(d_low)
                LOWS[d.name] = low_name
            case syntax.ConstantDecl():
                low_name = syntax.the_program.scope.fresh(d.name + LOW)
                d_low = syntax.ConstantDecl(low_name, d.sort, d.mutable)
                new_decls.append(d_low)
                syntax.the_program.scope.add_constant(d_low)
                LOWS[d.name] = low_name
            case syntax.FunctionDecl():
                low_name = syntax.the_program.scope.fresh(d.name + LOW)
                d_low = syntax.FunctionDecl(low_name, d.arity, d.sort, d.mutable)
                new_decls.append(d_low)
                syntax.the_program.scope.add_function(d_low)
                LOWS[d.name] = low_name
            case _:
                pass
    syntax.the_program.decls.extend(new_decls)

def low_expr(e: syntax.Expr) -> syntax.Expr:
    match e:
        case syntax.Id():
            if isinstance(syntax.the_program.scope.get(e.name), syntax.ConstantDecl):
                return syntax.Id(LOWS[e.name], n_new=e.n_new)
            else:
                return e
        case syntax.AppExpr():
            return syntax.AppExpr(LOWS[e.callee], tuple(low_expr(a) for a in e.args), n_new=e.n_new)
        case syntax.UnaryExpr():
            return syntax.UnaryExpr(e.op, low_expr(e.arg))
        case syntax.BinaryExpr():
            return syntax.BinaryExpr(e.op, low_expr(e.arg1), low_expr(e.arg2))
        case syntax.NaryExpr():
            return syntax.NaryExpr(e.op, tuple(low_expr(a) for a in e.args))
        case syntax.QuantifierExpr():
            with syntax.the_program.scope.in_scope(e.binder, [v.sort for v in e.binder.vs]):
                return syntax.QuantifierExpr(e.quant, e.get_vs(), low_expr(e.body))
        case syntax.IfThenElse():
            return syntax.IfThenElse(low_expr(e.branch), low_expr(e.then), low_expr(e.els))
        case syntax.Let():
            return syntax.Let(e.var, low_expr(e.val), low_expr(e.body))
        case _:
            return e

@dataclass(frozen=True)
class DisjunctiveCheck:
    n_states: int
    implications: List[Tuple[List[syntax.Expr], List[syntax.Expr]]]

    def check(self, s: solver.Solver) -> solver.CheckSatResult:
        tr = s.get_translator(self.n_states)
        for (hyp, cons) in self.implications:
            with s.new_frame():
                print('    >>> Hypotheses:')
                for h in hyp:
                    print('    >>>     %s' % h)
                    s.add(tr.translate_expr(h))
                print('    >>> Consequences:')
                for c in cons:
                    print('    >>>     %s' % c)
                    with s.new_frame():
                        s.add(tr.translate_expr(syntax.Not(c)))
                        if (res := s.check()) != solver.unsat:
                            if res == solver.sat:
                                print('========== COUNTER-EXAMPLE ==========')
                                print(tr.model_to_trace(s.model(), self.n_states))
                                print('=====================================')
                            return res
        return solver.unsat

class Squeezer:
    def __init__(self, cutoff: syntax.SqueezerCutoffDecl,
                 condition: syntax.SqueezerConditionDecl,
                 updates: Dict[str, syntax.SqueezerUpdateDecl],
                 candidate_var: syntax.SortedVar) -> None:
        self.cutoff = cutoff
        self.condition = condition
        self.updates = updates

        self.candidate_var = candidate_var
        self.condition_with_candidate = self._subst_candidate(self.condition.expr, self.condition.var)
    
    def _active_expr(self, e: syntax.Expr) -> syntax.Expr:
        match e:
            case syntax.QuantifierExpr():
                guard = all_active(e.get_vs(), self.candidate_var)
                new_body = self._active_expr(e.body)
                match e.quant:
                    case 'FORALL':
                        return syntax.QuantifierExpr(e.quant, e.binder.vs,
                                                    syntax.Implies(syntax.And(*guard), new_body))
                    case 'EXISTS':
                        return syntax.QuantifierExpr(e.quant, e.binder.vs,
                                                     syntax.And(*chain(guard, (new_body,))))
                    case _:
                        assert False
            case syntax.UnaryExpr():
                return syntax.UnaryExpr(e.op, self._active_expr(e.arg))
            case syntax.BinaryExpr():
                return syntax.BinaryExpr(e.op, self._active_expr(e.arg1), self._active_expr(e.arg2))
            case syntax.NaryExpr():
                return syntax.NaryExpr(e.op,
                                    tuple(self._active_expr(arg) for arg in e.args))
            case syntax.AppExpr():
                return syntax.AppExpr(e.callee,
                                    tuple(self._active_expr(arg) for arg in e.args),
                                    n_new=e.n_new)
            case syntax.IfThenElse():
                return syntax.IfThenElse(self._active_expr(e.branch), self._active_expr(e.then), self._active_expr(e.els))
            case syntax.Let():
                return syntax.Let(e.var, self._active_expr(e.val), self._active_expr(e.body))
            case _:
                return e

    def squeezer_expr(self) -> syntax.Expr:
        '''
        The squeezer expression, where the low vocabulary is denoted with the number of primes specified by `low_primes`
        '''

        conjuncts = [self.condition_with_candidate]
        for u in self.updates.values():
            expr = syntax.Eq(u.app_expr(lows=LOWS), self._subst_candidate(u.expr, u.params[-1]))
            if len(u.params) > 1:
                expr = syntax.QuantifierExpr('FORALL', u.params[:-1], expr)
            conjuncts.append(expr)
        
        return syntax.And(*conjuncts)
    
    def _subst_candidate(self, e: syntax.Expr, v: syntax.SortedVar) -> syntax.Expr:
        return syntax.subst(syntax.the_program.scope, e, {syntax.Id(v.name): syntax.Id(self.candidate_var.name)})

    def _closed(self) -> Iterator[syntax.Expr]:
        for u in self.updates.values():
            if u.sort == self.candidate_var.sort:
                totality = syntax.Neq(u.app_expr(lows=LOWS), syntax.Id(self.candidate_var.name))
                if len(u.params) > 1:
                    totality = syntax.QuantifierExpr('FORALL', u.params[:-1], totality)
                totality = self._active_expr(totality)
                yield totality

    def mu_initiation_check(self) -> DisjunctiveCheck:
        '''
        axioms & size > k & init => exists z. μ(z)
        '''

        return DisjunctiveCheck(1, [
            ([has_more_than(self.cutoff.bound, self.cutoff.sort)] + [init.expr for init in syntax.the_program.inits()],
             [syntax.QuantifierExpr('EXISTS', (self.condition.var,), self.condition.expr)])
        ])
    
    def mu_consecution_check(self) -> DisjunctiveCheck:
        '''
        axioms & axioms' & μ(z) & transitions => μ(z)'
        '''

        return DisjunctiveCheck(2, [
            ([self.condition_with_candidate, t],
             [syntax.New(self.condition_with_candidate)])
            for t in TRANSITIONS
        ])
    
    def state_preservation_check(self) -> DisjunctiveCheck:
        '''
        axioms_h & ν(z) => A_z[axioms_l] & [closed(z)]_l
        '''

        sq_expr = self.squeezer_expr()
        cons = [self._active_expr(low_expr(ax.expr)) for ax in syntax.the_program.axioms()] + list(self._closed())

        return DisjunctiveCheck(1, [([sq_expr], cons)])
    
    def init_preservation_check(self) -> DisjunctiveCheck:
        '''
        axioms_h & init_h & ν(z) => A_z[init_l]
        '''

        hyps = [init.expr for init in syntax.the_program.inits()] + [self.squeezer_expr()]
        
        return DisjunctiveCheck(1, [
            (hyps, [self._active_expr(low_expr(init.expr)) for init in syntax.the_program.inits()])
        ])

    def simulation_check(self) -> DisjunctiveCheck:
        '''
        axioms_h & axioms_h' & ν(z) & ν'(z) & transitions_h => A_z[transitions_l | idle_l]
        '''

        squeezer_expr = self.squeezer_expr()
        squeezer_expr_new = syntax.New(squeezer_expr)
        idle_low = self._active_expr(low_expr(IDLE))

        return DisjunctiveCheck(2, [
            ([squeezer_expr, squeezer_expr_new, t],
             [syntax.Or(self._active_expr(low_expr(t)), idle_low)])
            for t in TRANSITIONS
        ])

    def fault_preservation_check(self) -> DisjunctiveCheck:
        '''
        axioms_h & !satefy_h & ν(z) => A_z[!satefy_l]
        '''
        
        bad = syntax.Not(syntax.And(*(safety.expr for safety in syntax.the_program.safeties())))
        
        return DisjunctiveCheck(1, [
            ([bad, self.squeezer_expr()], [self._active_expr(low_expr(bad))])
        ])

    def run_checks(self, s: solver.Solver) -> None:
        print('Running checks...')
        checks: List[Tuple[str, DisjunctiveCheck]] = [
            ('μ-INITIATION:\n    axioms & size > %d & init => exists z. μ(z)' % (self.cutoff.bound), self.mu_initiation_check()),
            ('μ-CONSECUTION:\n    axioms & axioms\' & μ(z) & transitions => μ(z)\'', self.mu_consecution_check()),
            ('STATE PRESERVATION:\n    axioms_h & ν(z) => A_z[axioms_l] & [closed(z)]_l', self.state_preservation_check()),
            ('INIT PRESERVATION:\n    axioms_h & init_h & ν(z) => A_z[init_l]', self.init_preservation_check()),
            ('SIMULATION:\n    axioms_h & axioms_h\' & ν(z) & ν\'(z) & transitions_h => A_z[transitions_l | idle_l]', self.simulation_check()),
            ('FAULT PRESERVATION:\n    axioms_h & !satefy_h & ν(z) => A_z[!satefy_l]', self.fault_preservation_check())
        ]
        
        for (name, check) in checks:
            print(name)
            res = check.check(s)
            print('    ... ' + status(res))

def status(solver_status: solver.CheckSatResult) -> str:
    if solver_status == solver.unsat:
        return 'PASSED'
    if solver_status == solver.sat:
        return 'FAILED'
    return 'UNKNOWN'

def default_condition(sort: syntax.UninterpretedSort) -> syntax.SqueezerConditionDecl:
    return syntax.SqueezerConditionDecl(syntax.SortedVar('z', sort), syntax.TrueExpr)

def default_update(name: str, arity: Optional[syntax.Arity], sort: syntax.Sort, candidate_var: syntax.SortedVar) -> syntax.SqueezerUpdateDecl:
    if arity is None:
        return syntax.SqueezerUpdateDecl(name, (candidate_var,), sort, syntax.Id(name))
    else:
        vs = tuple(syntax.SortedVar('%s_%i' % (s, i + 1), s) for i, s in enumerate(arity))
        return syntax.SqueezerUpdateDecl(name, vs  + (candidate_var,), sort,
                               syntax.AppExpr(name, tuple(syntax.Id(v.name) for v in vs)))

def has_more_than(n: int, sort: syntax.UninterpretedSort) -> syntax.Expr:
    vs = tuple(syntax.SortedVar('%s_%i' % (sort.name, i) , sort) for i in range(1, n + 2))
    ineq = syntax.And(*(syntax.Neq(syntax.Id(x.name), syntax.Id(y.name)) for x, y in combinations(vs, 2)))
    return syntax.QuantifierExpr('EXISTS', vs, ineq)

def all_active(vs: Iterable[syntax.SortedVar], non_active: syntax.SortedVar) -> List[syntax.Expr]:
    return [syntax.Neq(syntax.Id(v.name), syntax.Id(non_active.name))
            for v in vs if v.sort == non_active.sort]

def squeezer() -> Squeezer:
    prog = syntax.the_program
    
    # Find squeezer cutoff
    cutoff: syntax.SqueezerCutoffDecl = prog.squeezer_cutoff()
    assert(cutoff is not None)
    # Add squeezer deletion condition
    condition: syntax.SqueezerConditionDecl = prog.squeezer_condition()
    if condition is None:
        condition = default_condition(cutoff.sort)
    # Add invariants to squeezer condition
    condition.expr = syntax.And(*chain((condition.expr,), (inv.expr for inv in prog.invs() if not inv.is_safety)))
    # Create candidate variable
    candidate = syntax.the_program.scope.fresh('cand')
    syntax.the_program.scope.add_constant(syntax.ConstantDecl(candidate, cutoff.sort, False))
    candidate_var = syntax.SortedVar(candidate, cutoff.sort)
    # Find squeezer updates
    updates: Dict[str, syntax.SqueezerUpdateDecl] = {}
    for d in prog.squeezer_updates():
        updates[d.name] = d
    # Print detected squeezer
    print('DETECTED SQUEEZER:')
    print('    %s' % cutoff)
    print('    %s' % condition)
    for u in updates.values():
        print('    %s' % u)
    print()
    # Add default squeezer updates for the rest + typecheck
    for c in prog.constants():
        if c.name in LOWS:
            if c.name not in updates:
                updates[c.name] = default_update(c.name, None, c.sort, candidate_var)
            else:
                assert(len(updates[c.name].params) == 1)
                assert(updates[c.name].sort == c.sort)
    for f in prog.functions():
        if f.name in LOWS:
            if f.name not in updates:
                updates[f.name] = default_update(f.name, f.arity, f.sort, candidate_var)
            else:
                assert(len(updates[f.name].params) == len(f.arity) + 1)
                assert(updates[f.name].sort == f.sort)
    for r in prog.relations():
        if r.name in LOWS:
            if r.name not in updates:
                updates[r.name] = default_update(r.name, r.arity, syntax.BoolSort, candidate_var)
            else:
                assert(len(updates[r.name].params) == len(r.arity) + 1)
                assert(updates[r.name].sort == syntax.BoolSort)
    
    return Squeezer(cutoff, condition, updates, candidate_var)
    