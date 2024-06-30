from typing import Iterable, List, Optional, Dict, Tuple, Union, Iterator
import syntax
import solver
from itertools import combinations, chain
import logging
from dataclasses import dataclass
import utils

logger = logging.getLogger(__name__)

LOW = '_l'

def add_low_to_program() -> None:
    """
    Adds 'low' versions of declarations to the program, and saves the mapping from
    the original versions to the 'low' versions in `LOWS`. Also saves the original transition
    formulas in `TRANSITIONS`, and an idle transition formula in `IDLE`.

    The above is saved before adding the 'low' declarations because when a transition formula is generated,
    it states that unmodified relations / constants / functions are not changed, and thus adding 'low' versions
    affects newly generated transition formulas in an undesirable way.
    """

    global LOWS
    global TRANSITIONS
    global IDLE

    TRANSITIONS = {t.name: t.as_twostate_formula(syntax.the_program.scope) for t in syntax.the_program.transitions()}
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

def print_verbose(x) -> None:
    if utils.args.verbose:
        print(x)

@dataclass(frozen=True)
class Consequence:
    n_states: int
    vs: Tuple[syntax.SortedVar]
    hyp: List[syntax.Expr]
    cons: List[syntax.Expr]

    def check(self, s: solver.Solver) -> solver.CheckSatResult:
        tr = s.get_translator(self.n_states)
    
        print_verbose('    >>> HYPOTHESES:')
        for h in self.hyp:
            print_verbose('    >>>     %s' % h)
        print_verbose('    >>> CONSEQUENCES:')
        for c in self.cons:
            print_verbose('    >>>     %s' % c)
            assertions = self.hyp + [syntax.Not(c)]
            with s.new_frame():
                s.add(tr.translate_expr(syntax.Exists(self.vs, syntax.And(*assertions))))
                if (res := s.check()) != solver.unsat:
                    if res == solver.sat and utils.args.print_cex:
                        print('========== COUNTER-EXAMPLE ==========')
                        print(tr.model_to_trace(s.model(), self.n_states))
                        print('=====================================')
                    return res
        return solver.unsat

@dataclass(frozen=True)
class Consequences:
    checks: List[Consequence]

    def check(self, s: solver.Solver) -> solver.CheckSatResult:
        for c in self.checks:
            if (res := c.check(s)) != solver.unsat:
                return res
        return solver.unsat

class Squeezer:
    def __init__(self,
                 cutoff_sort: syntax.CutoffSortDecl,
                 cutoff_bound: syntax.CutoffBoundDecl,
                 condition: syntax.CutoffConditionDecl,
                 updates: Dict[str, syntax.CutoffUpdateDecl],
                 hints: Dict[str, syntax.CutoffHintDecl],
                 candidate_var: syntax.SortedVar) -> None:
        self.cutoff_sort = cutoff_sort.sort
        self.cutoff_bound = cutoff_bound.bound
        self.condition = condition
        self.updates = updates
        self.hints = hints

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
                expr = syntax.Forall(u.params[:-1], expr)
            conjuncts.append(expr)
        
        return syntax.And(*conjuncts)
    
    def _subst_candidate(self, e: syntax.Expr, v: syntax.SortedVar) -> syntax.Expr:
        return syntax.subst(syntax.the_program.scope, e, {syntax.Id(v.name): syntax.Id(self.candidate_var.name)})

    def _closed(self) -> Iterator[syntax.Expr]:
        for u in self.updates.values():
            if u.sort == self.candidate_var.sort:
                totality = syntax.Neq(u.app_expr(lows=LOWS), syntax.Id(self.candidate_var.name))
                if len(u.params) > 1:
                    totality = syntax.Forall(u.params[:-1], totality)
                totality = self._active_expr(totality)
                yield totality

    def _hinted_transition_checks(self) -> Iterator[Consequence]:
        squeezer_expr = self.squeezer_expr()
        squeezer_expr_new = syntax.New(squeezer_expr)
        idle_low = self._active_expr(low_expr(IDLE))

        for name, t in TRANSITIONS.items():
            if name not in self.hints:
                t_l = self._active_expr(low_expr(t))
                yield Consequence(2, (self.candidate_var,), [squeezer_expr, squeezer_expr_new, t], [syntax.Or(t_l, idle_low)])
            else:
                hint = self.hints[name]
                if isinstance(t, syntax.QuantifierExpr):
                    t_params: Tuple[syntax.SortedVar, ...] = t.get_vs()
                    t_expr = t.body
                else:
                    t_params: Tuple[syntax.SortedVar, ...] = ()
                    t_expr = t
                high_vs = hint.params[:len(t_params)]
                low_vs = hint.params[len(t_params):len(t_params) * 2]
                cand_v = hint.params[len(t_params) * 2]
                # Totality
                t_subst = syntax.subst(syntax.the_program.scope, t_expr,
                                       {syntax.Id(v.name): syntax.Id(high_vs[i].name) for i, v in enumerate(t_params)})
                hint_subst = syntax.subst(syntax.the_program.scope, hint.expr,
                                          {syntax.Id(cand_v.name): syntax.Id(self.candidate_var.name)})
                hint_quant = syntax.Exists(low_vs, hint_subst)
                yield Consequence(2, (self.candidate_var,) + high_vs, [squeezer_expr, squeezer_expr_new, t_subst], [hint_quant])
                # Sufficiency
                t_l_expr = self._active_expr(low_expr(t_expr))
                t_l_subst = syntax.subst(syntax.the_program.scope, t_l_expr,
                                         {syntax.Id(v.name): syntax.Id(low_vs[i].name) for i, v in enumerate(t_params)})
                yield Consequence(2, (self.candidate_var,) + high_vs + low_vs,
                                  [squeezer_expr, squeezer_expr_new, t_subst, hint_subst],
                                  [syntax.Or(t_l_subst, idle_low)])

    def mu_initiation_check(self) -> Consequence:
        '''
        axioms & size > k & init => exists z. μ(z)
        '''

        return Consequence(1, (self.candidate_var,),
                           [has_more_than(self.cutoff_bound, self.cutoff_sort)] + [init.expr for init in syntax.the_program.inits()],
                           [syntax.Exists((self.condition.var,), self.condition.expr)])
    
    def mu_consecution_check(self) -> Consequences:
        '''
        axioms & axioms' & μ(z) & transitions => μ(z)'
        '''

        return Consequences([
            Consequence(2, (self.candidate_var,),
                        [self.condition_with_candidate, t],
                        [syntax.New(self.condition_with_candidate)])
            for t in TRANSITIONS.values()
        ])
    
    def projectability_check(self) -> Consequence:
        '''
        axioms^h & ν(z) => closed(z)^l
        '''

        sq_expr = self.squeezer_expr()
        cons = list(self._closed())

        return Consequence(1, (self.candidate_var,), [sq_expr], cons)
    
    def axiom_preservation_check(self) -> Consequence:
        r'''
        axioms^h & ν(z) => [axioms^l]\z
        '''

        sq_expr = self.squeezer_expr()
        cons = [self._active_expr(low_expr(ax.expr)) for ax in syntax.the_program.axioms()]

        return Consequence(1, (self.candidate_var,), [sq_expr], cons)
    
    def init_preservation_check(self) -> Consequence:
        r'''
        axioms^h & init^h & ν(z) => [init^l]\z
        '''

        hyps = [init.expr for init in syntax.the_program.inits()] + [self.squeezer_expr()]
        
        return Consequence(1, (self.candidate_var,), hyps, [self._active_expr(low_expr(init.expr)) for init in syntax.the_program.inits()])

    def simulation_check(self) -> Consequences:
        r'''
        axioms^h & axioms^h' & ν(z) & ν'(z) & transitions^h => [transitions^l | idle^l]\z
        '''

        return Consequences(list(self._hinted_transition_checks()))

    def fault_preservation_check(self) -> Consequences:
        r'''
        axioms^h & !satefy^h & ν(z) => [!satefy^l]\z
        '''
        
        bad = syntax.Not(syntax.And(*(safety.expr for safety in syntax.the_program.safeties())))
        
        return Consequence(1, (self.candidate_var,), [bad, self.squeezer_expr()], [self._active_expr(low_expr(bad))])

    def run_checks(self, s: solver.Solver) -> None:
        print('Running checks:')
        print()

        checks: List[Tuple[str, Union[Consequence, Consequences]]] = [
            ('INIT PRESERVATION:\n    axioms^h & init^h & ν(z) => [init^l]\\z', self.init_preservation_check()),
            ('TRANSITION PRESERVATION:\n    axioms^h & axioms^h\' & ν(z) & ν\'(z) & transitions^h => [transitions^l | idle^l]\\z', self.simulation_check()),
            ('FAULT PRESERVATION:\n    axioms^h & !satefy^h & ν(z) => [!satefy^l]\\z', self.fault_preservation_check()),
            ('PROJECTABILITY:\n    axioms^h & ν(z) => closed(z)^l', self.projectability_check()),
            ('Γ-PRESERVATION:\n    axioms^h & ν(z) => [axioms^l]\\z', self.axiom_preservation_check()),
            ('μ-INITIATION:\n    axioms & size > %d & init => exists z. μ(z)' % (self.cutoff_bound), self.mu_initiation_check()),
            ('μ-CONSECUTION:\n    axioms & axioms\' & μ(z) & transitions => μ(z)\'', self.mu_consecution_check()),
        ]
        
        for (name, check) in checks:
            print(name)
            res = check.check(s)
            print('    ... ' + status(res))
            print()
            if res == solver.unknown:
                print('unknown!')
                return
            if res == solver.sat:
                print('failed!')
                return
        
        print('all ok!')

def status(solver_status: solver.CheckSatResult) -> str:
    if solver_status == solver.unsat:
        return 'PASSED'
    if solver_status == solver.sat:
        return 'FAILED'
    return 'UNKNOWN'

def default_condition(sort: syntax.UninterpretedSort) -> syntax.CutoffConditionDecl:
    consts = [c.name for c in syntax.the_program.constants() if c.sort == sort and c.name in LOWS]
    assert 'z' not in consts, "cannot use default deletion condition if a constant named \'z\' exists"
    return syntax.CutoffConditionDecl(syntax.SortedVar('z', sort),
                                        syntax.And(*(syntax.Neq(syntax.Id(c), syntax.Id('z')) for c in consts)))

def default_bound(sort: syntax.UninterpretedSort) -> syntax.CutoffBoundDecl:
    return syntax.CutoffBoundDecl(sum(1 for c in syntax.the_program.constants() if c.sort == sort and c.name in LOWS))

def default_update(name: str, arity: Optional[syntax.Arity], sort: syntax.Sort, candidate_var: syntax.SortedVar) -> syntax.CutoffUpdateDecl:
    if arity is None:
        return syntax.CutoffUpdateDecl(name, (candidate_var,), sort, syntax.Id(name))
    else:
        vs = tuple(syntax.SortedVar('%s_%i' % (s, i + 1), s) for i, s in enumerate(arity))
        return syntax.CutoffUpdateDecl(name, vs  + (candidate_var,), sort,
                               syntax.AppExpr(name, tuple(syntax.Id(v.name) for v in vs)))

def has_more_than(n: int, sort: syntax.UninterpretedSort) -> syntax.Expr:
    vs = tuple(syntax.SortedVar('%s_%i' % (sort.name, i) , sort) for i in range(1, n + 2))
    ineq = syntax.And(*(syntax.Neq(syntax.Id(x.name), syntax.Id(y.name)) for x, y in combinations(vs, 2)))
    return syntax.Exists(vs, ineq)

def all_active(vs: Iterable[syntax.SortedVar], non_active: syntax.SortedVar) -> List[syntax.Expr]:
    return [syntax.Neq(syntax.Id(v.name), syntax.Id(non_active.name))
            for v in vs if v.sort == non_active.sort]

def squeezer() -> Squeezer:
    prog = syntax.the_program
    
    # Find squeezer cutoff
    cutoff_sort: syntax.CutoffSortDecl = prog.squeezer_cutoff_sort()
    assert(cutoff_sort is not None)
    cutoff_bound: syntax.CutoffBoundDecl = prog.squeezer_cutoff_bound()
    if cutoff_bound is None:
        cutoff_bound = default_bound(cutoff_sort.sort)
    # Add squeezer deletion condition
    condition: syntax.CutoffConditionDecl = prog.squeezer_condition()
    if condition is None:
        condition = default_condition(cutoff_sort.sort)
    else:
        assert condition.var.sort == cutoff_sort.sort, 'condition parameter sort does not match cutoff sort'
    # Add invariants to squeezer condition
    condition.expr = syntax.And(*chain((condition.expr,), (inv.expr for inv in prog.invs() if not inv.is_safety)))
    # Create candidate variable
    candidate = syntax.the_program.scope.fresh('cand')
    candidate_var = syntax.SortedVar(candidate, cutoff_sort.sort)
    # Find squeezer updates and hints
    updates: Dict[str, syntax.CutoffUpdateDecl] = {}
    for d in prog.squeezer_updates():
        updates[d.name] = d
    hints: Dict[str, syntax.CutoffHintDecl] = {d.name: d for d in prog.squeezer_hints()}
    # Add default squeezer updates for the rest + typecheck
    for c in prog.constants():
        if c.name in LOWS:
            if c.name not in updates:
                updates[c.name] = default_update(c.name, None, c.sort, candidate_var)
            else:
                assert len(updates[c.name].params) == 1, \
                    'update for %s has wrong number of parameters' % c.name
                assert updates[c.name].params[0].sort == cutoff_sort.sort, \
                    'update for %s has wrong candidate sort' % c.name
                assert updates[c.name].sort == c.sort, \
                    'update for %s has wrong sort' % c.name
    for f in prog.functions():
        if f.name in LOWS:
            if f.name not in updates:
                updates[f.name] = default_update(f.name, f.arity, f.sort, candidate_var)
            else:
                u = updates[f.name]
                assert len(u.params) == len(f.arity) + 1, \
                    'update for %s has wrong number of parameters' % f.name
                assert all(s == u.params[i].sort for i, s in enumerate(f.arity)), \
                    'update for %s has wrong parameter sorts' % f.name
                assert u.params[len(f.arity)].sort == cutoff_sort.sort, \
                    'update for %s has wrong candidate sort' % f.name
                assert updates[f.name].sort == f.sort, \
                    'update for %s has wrong sort' % f.name
    for r in prog.relations():
        if r.name in LOWS:
            if r.name not in updates:
                updates[r.name] = default_update(r.name, r.arity, syntax.BoolSort, candidate_var)
            else:
                u = updates[r.name]
                assert len(u.params) == len(r.arity) + 1, \
                    'update for %s has wrong number of parameters' % r.name
                assert all(s == u.params[i].sort for i, s in enumerate(r.arity)), \
                    'update for %s has wrong parameter sorts' % r.name
                assert u.params[len(r.arity)].sort == cutoff_sort.sort, \
                    'update for %s has wrong candidate sort' % r.name
                assert updates[r.name].sort == syntax.BoolSort, \
                    'update for %s has wrong sort' % r.name
    for name, t in TRANSITIONS.items():
        if name in hints:
            h = hints[name]
            if isinstance(t, syntax.QuantifierExpr) and t.quant == 'EXISTS':
                vs = t.get_vs()
                assert len(h.params) == len(vs) * 2 + 1, \
                    'hint for %s has wrong number of paramters' % h.name
                assert all(v.sort == h.params[i].sort and v.sort == h.params[len(vs) + i].sort for i, v in enumerate(vs)), \
                    'hint for %s has wrong parameter sorts' % h.name
                assert h.params[len(vs) * 2].sort == cutoff_sort.sort, \
                    'hint for %s has wrong candidate sort' % h.name
            else:
                assert len(h.params) == 1, \
                    'hint for %s has wrong number of paramters' % h.name
                assert h.params[0].sort == cutoff_sort.sort, \
                    'hint for %s has wrong candidate sort' % h.name

    # Print detected squeezer
    print('Detected cutoff:')
    print('    %s' % cutoff_sort)
    print('    %s' % cutoff_bound)
    print('Detected μ-update:')
    print('    %s' % condition)
    for u in updates.values():
        print('    %s' % u)
    print()

    return Squeezer(cutoff_sort, cutoff_bound, condition, updates, hints, candidate_var)
