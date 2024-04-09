from typing import Iterable, List, Optional, Dict, Tuple, Set, Generator
import syntax
import solver
from itertools import combinations, chain

CANDIDATE = 'sq_cand'
LOW = '_low'

def add_low_to_program() -> Set[str]:
    lows: Set[str] = set()
    new_decls = []
    for d in syntax.the_program.decls:
        match d:
            case syntax.RelationDecl():
                d_low = syntax.RelationDecl(d.name + LOW, d.arity, d.mutable)
                new_decls.append(d_low)
                syntax.the_program.scope.add_relation(d_low)
                lows.add(d_low.name)
            case syntax.ConstantDecl():
                d_low = syntax.ConstantDecl(d.name + LOW, d.sort, d.mutable)
                new_decls.append(d_low)
                syntax.the_program.scope.add_constant(d_low)
                lows.add(d_low.name)
            case syntax.FunctionDecl():
                d_low = syntax.FunctionDecl(d.name + LOW, d.arity, d.sort, d.mutable)
                new_decls.append(d_low)
                syntax.the_program.scope.add_function(d_low)
                lows.add(d_low.name)
            case _:
                pass
    syntax.the_program.decls.extend(new_decls)

    return lows

def active_expr(e: syntax.Expr, cand: syntax.SortedVar) -> syntax.Expr:
    match e:
        case syntax.QuantifierExpr():
            guard = all_active(e.binder.vs, cand)
            new_body = active_expr(e.body, cand)
            match e.quant:
                case 'FORALL':
                    return syntax.QuantifierExpr(e.quant, e.binder.vs,
                                                 syntax.Implies(syntax.And(*guard), new_body))
                case 'EXISTS':
                    return syntax.QuantifierExpr(e.quant, e.binder.vs,
                                                 syntax.And(new_body, *guard))
        case syntax.UnaryExpr():
            return syntax.UnaryExpr(e.op,
                                     active_expr(e.arg, cand))
        case syntax.BinaryExpr():
            return syntax.BinaryExpr(e.op,
                                     active_expr(e.arg1, cand),
                                     active_expr(e.arg2, cand))
        case syntax.NaryExpr():
            return syntax.NaryExpr(e.op,
                                   tuple(active_expr(arg, cand) for arg in e.args))
        case syntax.AppExpr():
            return syntax.AppExpr(e.callee,
                                  tuple(active_expr(arg, cand) for arg in e.args),
                                  n_new=e.n_new)
        case syntax.IfThenElse():
            return syntax.IfThenElse(active_expr(e.branch, cand),
                                     active_expr(e.then, cand),
                                     active_expr(e.els, cand))
        case syntax.Let():
            return syntax.Let(e.var,
                              active_expr(e.val, cand),
                              active_expr(e.body, cand))
        case _:
            return e

def low_expr(e: syntax.Expr) -> syntax.Expr:
    match e:
        case syntax.Id():
            if isinstance(syntax.the_program.scope.get(e.name), syntax.ConstantDecl):
                return syntax.Id(e.name + LOW)
            else:
                return e
        case syntax.AppExpr():
            return syntax.AppExpr(e.callee + LOW, tuple(low_expr(a) for a in e.args), n_new=e.n_new)
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

class Squeezer:
    def __init__(self, cutoff: syntax.SqueezerCutoffDecl,
                 condition: syntax.SqueezerConditionDecl,
                 updates: Dict[str, syntax.SqueezerUpdateDecl]) -> None:
        self.cutoff = cutoff
        self.condition = condition
        self.updates = updates
        self.candidate_var = syntax.SortedVar(CANDIDATE, self.cutoff.sort)
        self.condition_with_candidate = subst_candidate(self.condition.expr, self.condition.var)
    
    def squeezer_expr(self) -> syntax.Expr:
        '''
        The squeezer expression, where the low vocabulary is denoted with the number of primes specified by `low_primes`
        '''

        conjuncts = [self.condition_with_candidate]
        for u in self.updates.values():
            expr = syntax.Eq(u.app_expr(suffix=LOW), subst_candidate(u.expr, u.params[-1]))
            if len(u.params) > 1:
                expr = syntax.QuantifierExpr('FORALL', u.params[:-1], expr)
            conjuncts.append(expr)
        
        return syntax.And(*conjuncts)
    
    def _closed(self):
        for u in self.updates.values():
            if u.sort == self.candidate_var.sort:
                totality = syntax.Neq(u.app_expr(suffix=LOW), syntax.Id(self.candidate_var.name))
                if len(u.params) > 1:
                    totality = syntax.QuantifierExpr('FORALL', u.params[:-1], totality)
                totality = active_expr(totality, self.candidate_var)
                yield totality

    def mu_initiation_check(self, s: solver.Solver) -> solver.CheckSatResult:
        '''
        axioms & size > k & init => exists z. μ(z)
        '''

        tr = s.get_translator(1)
        with s.new_frame():
            s.add(tr.translate_expr(has_more_than(self.cutoff.bound, self.cutoff.sort)))
            for init in syntax.the_program.inits():
                s.add(tr.translate_expr(init.expr))
            s.add(tr.translate_expr(syntax.Not(syntax.QuantifierExpr('EXISTS', (self.condition.var,), self.condition.expr))))
            return s.check()
    
    def mu_consecution_check(self, s: solver.Solver) -> solver.CheckSatResult:
        '''
        axioms & axioms' & μ(z) & transitions => μ(z)'
        '''

        tr = s.get_translator(2)
        with s.new_frame():
            s.add(tr.translate_expr(
                syntax.QuantifierExpr(
                    'EXISTS',
                    (self.candidate_var,),
                    syntax.And(
                        self.condition_with_candidate,
                        syntax.New(syntax.Not(self.condition_with_candidate))
                    )
            )))
            for t in syntax.the_program.transitions():
                with s.new_frame():
                    s.add(tr.translate_expr(t.as_twostate_formula(syntax.the_program.scope)))
                    if (res := s.check()) != solver.unsat:
                        return res
        
        return solver.unsat
    
    def state_preservation_check(self, s: solver.Solver) -> solver.CheckSatResult:
        '''
        axioms_h & ν(z) => A_z[axioms_l] & [closed(z)]_l
        '''

        tr = s.get_translator(1)
        with s.new_frame():
            # Check low axioms
            for ax in syntax.the_program.axioms():
                with s.new_frame():
                    sq_and_not_ax = syntax.And(
                        self.squeezer_expr(),
                        syntax.Not(active_expr(low_expr(ax.expr), self.candidate_var))
                    )
                    s.add(tr.translate_expr(syntax.QuantifierExpr('EXISTS', (self.candidate_var,), sq_and_not_ax)))
                    if (res := s.check()) != solver.unsat:
                        return res
            # Check totality of functions
            for total in self._closed():
                with s.new_frame():
                    sq_and_not_total = syntax.And(
                        self.squeezer_expr(),
                        syntax.Not(total)
                    )
                    s.add(tr.translate_expr(syntax.QuantifierExpr('EXISTS', (self.candidate_var,), sq_and_not_total)))
                    if (res := s.check()) != solver.unsat:
                        return res
        return solver.unsat
    
    def run_checks(self, s: solver.Solver) -> None:
        print('Running checks...')
        print('μ-INITIATION:\n    axioms & size > %d & init => exists z. μ(z) .......... ' % (self.cutoff.bound), end='')
        print(status(self.mu_initiation_check(s)))
        print('μ-CONSECUTION:\n    axioms & axioms\' & μ(z) & transitions => μ(z)\' .......... ', end='')
        print(status(self.mu_consecution_check(s)))
        print('STATE PRESERVATION:\n    axioms_h & ν(z) => A_z[axioms_l] & [closed(z)]_l .......... ', end='')
        print(status(self.state_preservation_check(s)))

def status(solver_status: solver.CheckSatResult) -> str:
    if solver_status == solver.unsat:
        return 'PASSED'
    if solver_status == solver.unsat:
        return 'FAILED'
    return 'UNKNOWN'

def subst_candidate(e: syntax.Expr, v: syntax.SortedVar) -> syntax.Expr:
    return syntax.subst(syntax.the_program.scope, e, {syntax.Id(v.name): syntax.Id(CANDIDATE)})

def default_condition(sort: syntax.UninterpretedSort) -> syntax.SqueezerConditionDecl:
    return syntax.SqueezerConditionDecl(syntax.SortedVar('z', sort), syntax.TrueExpr)

def default_update(name: str, arity: Optional[syntax.Arity], sort: syntax.Sort, delete_sort: syntax.UninterpretedSort) -> syntax.SqueezerUpdateDecl:
    cand_var = syntax.SortedVar(CANDIDATE, delete_sort)
    if arity is None:
        return syntax.SqueezerUpdateDecl(name, (cand_var,), sort, syntax.Id(name))
    else:
        vs = tuple(syntax.SortedVar('%s_%i' % (s, i + 1), s) for i, s in enumerate(arity))
        return syntax.SqueezerUpdateDecl(name, vs  + (cand_var,), sort,
                               syntax.AppExpr(name, tuple(syntax.Id(v.name) for v in vs)))

def has_more_than(n: int, sort: syntax.UninterpretedSort) -> syntax.Expr:
    vs = tuple(syntax.SortedVar('%s_%i' % (sort.name, i) , sort) for i in range(1, n + 2))
    ineq = syntax.And(*(syntax.Neq(syntax.Id(x.name), syntax.Id(y.name)) for x, y in combinations(vs, 2)))
    return syntax.QuantifierExpr('EXISTS', vs, ineq)

def all_active(vs: Iterable[syntax.SortedVar], non_active: syntax.SortedVar) -> List[syntax.Expr]:
    return [syntax.Neq(syntax.Id(v.name), syntax.Id(non_active.name))
            for v in vs if v.sort == non_active.sort]

def squeezer(lows: Set[str]) -> Squeezer:
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
        if c.name not in lows:
            if c.name not in updates:
                updates[c.name] = default_update(c.name, None, c.sort, cutoff.sort)
            else:
                assert(len(updates[c.name].params) == 1)
                assert(updates[c.name].sort == c.sort)
    for f in prog.functions():
        if f.name not in lows:
            if f.name not in updates:
                updates[f.name] = default_update(f.name, f.arity, f.sort, cutoff.sort)
            else:
                assert(len(updates[f.name].params) == len(f.arity) + 1)
                assert(updates[f.name].sort == f.sort)
    for r in prog.relations():
        if r.name not in lows:
            if r.name not in updates:
                updates[r.name] = default_update(r.name, r.arity, syntax.BoolSort, cutoff.sort)
            else:
                assert(len(updates[r.name].params) == len(r.arity) + 1)
                assert(updates[r.name].sort == syntax.BoolSort)
    
    return Squeezer(cutoff, condition, updates)
    