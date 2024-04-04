from typing import Iterable, List, Optional, Dict, Tuple
import syntax
import solver
from itertools import combinations, chain

CANDIDATE = 'sq_cand'

class Squeezer:
    def __init__(self, cutoff: syntax.SqueezerCutoffDecl, condition: syntax.SqueezerConditionDecl, updates: Dict[str, syntax.SqueezerUpdateDecl]) -> None:
        self.cutoff = cutoff
        self.condition = condition
        self.updates = updates
    
    def squeezer_expr(self, low_primes: int) -> syntax.Expr:
        '''
        The squeezer expression, where the low vocabulary is denoted with the number of primes specified by `low_primes`
        '''

        conjuncts = [subst_candidate(self.condition.expr, self.condition.var)]
        conjuncts.extend(self.invariants)
        for u in self.updates.values():
            vs = u.params[:-1]
            vs_exprs = tuple(syntax.Id(v.name) for v in vs)
            
            if vs:
                body = syntax.Eq(syntax.AppExpr(u.name, vs_exprs, n_new=low_primes),
                                 subst_candidate(u.expr, u.params[-1]))
                conjuncts.append(syntax.QuantifierExpr('FORALL', vs, body))
            else:
                conjuncts.append(syntax.Eq(syntax.Id(u.name, n_new=low_primes),
                                           subst_candidate(u.expr, u.params[-1])))
        
        return syntax.And(*conjuncts)
    
    def pre_expr(self) -> Tuple[syntax.Expr]:
        return tuple(chain(
            (ax.expr for ax in syntax.the_program.axioms()),
            (inv.expr for inv in syntax.the_program.invs()),
            (has_more_than(self.cutoff.bound, self.cutoff.sort),)
        ))

    def initiation_check(self, s: solver.Solver) -> List[syntax.Expr]:
        tr = s.get_translator(1)
        with s.new_frame():
            for ax in syntax.the_program.axioms():
                s.add(tr.translate_expr(ax.expr))
            for init in syntax.the_program.inits():
                s.add(tr.translate_expr(init.expr))
            for inv in syntax.the_program.invs():
                with s.new_frame():
                    s.add(tr.translate_expr(syntax.Not(inv.expr)))
                    res = s.check()
                    if res != solver.unsat:
                        return res
        return solver.unsat
    
    def consecution_check(self, s: solver.Solver) -> List[syntax.Expr]:
        tr = s.get_translator(2)
        with s.new_frame():
            for e in self.pre_expr():
                s.add(tr.translate_expr(e))
            for trans in syntax.the_program.transitions():
                for inv in syntax.the_program.invs():
                    with s.new_frame():
                        s.add(tr.translate_expr(trans.as_twostate_formula()))
                        s.add(tr.translate_expr(syntax.Not(inv.expr)))
                        res = s.check()
                        if res != solver.unsat:
                            return res
        return solver.unsat

    def delete_candidate_check(self, s: solver.Solver) -> solver.CheckSatResult:
        tr = s.get_translator(1)
        with s.new_frame():
            for e in self.pre_expr():
                s.add(tr.translate_expr(e))
            s.add(tr.translate_expr(syntax.Not(syntax.QuantifierExpr('EXISTS', (self.condition.var,), self.condition.expr))))
            return s.check()
    
    def run_checks(self, s: solver.Solver) -> None:
        print('Running checks...')
        print('INITIATION:\n    axioms & init => inv... ', end='')
        print(status(self.initiation_check(s)))
        print('CONSECUTION:\n     axioms & inv & size & tr => inv\'... ', end='')
        print(status(self.initiation_check(s)))
        print('DELETE-CANDIDATE:\n     axioms & inv & size => exists z. condition... ', end='')
        print(status(self.delete_candidate_check(s)))

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

def squeezer() -> Squeezer:
    prog = syntax.the_program
    
    # Find squeezer cutoff
    cutoff: syntax.SqueezerCutoffDecl = prog.squeezer_cutoff()
    assert(cutoff is not None)
    # Add squeezer deletion condition
    condition: syntax.SqueezerConditionDecl = prog.squeezer_condition()
    if condition is None:
        condition = default_condition(cutoff.sort)
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
        if c.name not in updates:
            updates[c.name] = default_update(c.name, None, c.sort, cutoff.sort)
        else:
            assert(len(updates[c.name].params) == 1)
            assert(updates[c.name].sort == c.sort)
    for f in prog.functions():
        if f.name not in updates:
            updates[f.name] = default_update(f.name, f.arity, f.sort, cutoff.sort)
        else:
            assert(len(updates[f.name].params) == len(f.arity) + 1)
            assert(updates[f.name].sort == f.sort)
    for r in prog.relations():
        if r.name not in updates:
            updates[r.name] = default_update(r.name, r.arity, syntax.BoolSort, cutoff.sort)
        else:
            assert(len(updates[r.name].params) == len(r.arity) + 1)
            assert(updates[r.name].sort == syntax.BoolSort)
    
    return Squeezer(cutoff, condition, updates)
    