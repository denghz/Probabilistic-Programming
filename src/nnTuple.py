from wolframclient.evaluation import WolframLanguageSession
from wolframclient.language import wl, wlexpr
from wolframclient.deserializers import WXFConsumer, binary_deserialize
from wolframclient.serializers import export, wolfram_encoder
import wolframclient
import numbers
from nnDiff import countableManySolution
import sys
import itertools
functions1 = ("Sin", "Cos", "Tan", "Exp", "Log", "Minus", "Inv")
functions2 = ("Plus", "Subtract", "Times")
class Func:
    def __init__(self, pn):
        self.name = pn[0]
        self.arg1 = None
        self.arg2 = None
        del(pn[0])
        if self.name in functions1:
            self.arg1 = Func(pn)
        if self.name in functions2:
            self.arg1 = Func(pn)
            self.arg2 = Func(pn)
    def __str__(self):
        if self.arg1 == None and self.arg2 == None:
            return self.name
        return self.name + "[" + str(self.arg1) + (", " + (str(self.arg2)) if self.arg2 is not None else "") + "]" 

def nnTuple(e,vs):
    with WolframLanguageSession() as session:
        session.evaluate("Inv[zzz_] := 1/zzz")
        variables = list(map(lambda x:x[0], vs))
        ranges = list(map(lambda x:x[1:], vs))
        def chunks4(lst):
            for i in range(0, len(lst), 4):
                yield tuple(lst[i:i + 4])
        ranges = list(map(lambda x: list(chunks4(x)), ranges))
        print("nnTuple variable " + str(variables))
        
        print("nnTuple ranges " + str(ranges))
        def rangeToWlexpr(var, lb, lbt, ub, ubt):
            lbt = '<' if lbt == 'Open' else '<='
            ubt = '<' if ubt == 'Open' else '<='
            lb = '-Infinity' if lb == None else str(lb)
            ub = 'Infinity' if ub == None else str(ub)
            return wlexpr(lb+lbt+var+ubt+ub)
        conds = []
        for i in range(len(variables)):
            var = variables[i]
            conds.append(wl.Or(*map(lambda r:rangeToWlexpr(var, *r), ranges[i])))
        wlvs = list(map(wlexpr,variables))
        fs = list(map(lambda x:wlexpr(str(Func(x))), e))
        print("nnTuple exprs " + str(fs))
        session.evaluate("JDotTransJ[x1_, var_] := Block[{M = ResourceFunction[\"JacobianMatrix\"][x1, var]},Det[M . Transpose[M]]]")
        session.evaluate("Jaco[x1_, var_] := ResourceFunction[\"JacobianMatrix\"][x1, var]")
        jDotTransJ = session.evaluate(wl.Global.JDotTransJ(fs, wlvs))
        print("nnTuple Det(A*A^T) " + str(jDotTransJ))
        jacobian = session.evaluate(wl.Global.Jaco(fs,wlvs))
        print("nnTuple Jacobian " + str(jacobian))
        jacobianList = [element for tupl in jacobian for element in tupl]
        isContinuous = session.function("FunctionContinuous")
        isDeriCont = all(list(map(lambda x:isContinuous([x] + conds,wlvs), jacobianList)))
        print("nnTuple if all deri conts " + str(isDeriCont))
        if not isDeriCont:
            return False
        eq = wl.LessEqual(jDotTransJ, 0)
        res = session.evaluate(wl.Solve(wl.And([eq] + conds), wlvs, wl.Reals))
        print("nnTuple solution of det(A*A^T) < 0 " + str(res))
        detGt0 = countableManySolution(res, variables)
        print("nnTuple solution of det(A*A^T) < 0 countable " + str(detGt0))
        if not detGt0:
            return False
        
        return True

        # Y depends on X
        
if __name__ == "__main__":
    
    spl = lambda lst, delim: [list(y) for x, y in itertools.groupby(lst, lambda z: z == delim) if not x]
    args = sys.argv[1:]
    exp = []
    vs = []
    if args == []:
        exp = [["Plus", "x", "y"], ["Plus", "x", "Minus", "y"]]
        vs = vs = [['x'], ['y']]
    else:
        res = spl(args, "||")
        exp = res[0]
        exp = spl (exp, "##")
        vs = res[1]
        vs = spl(vs, "##")
    print(nnTuple(exp,vs), file=sys.stderr)