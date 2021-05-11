from wolframclient.evaluation import WolframLanguageSession
from wolframclient.language import wl, wlexpr
from wolframclient.deserializers import WXFConsumer, binary_deserialize
from wolframclient.serializers import export, wolfram_encoder
import wolframclient
import numbers

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


# falseEmp = wlexpr("Solve[Sin[x] + Cos[y] == 0, {x,y}, Reals]")
# trueEmp = wlexpr("Solve[Sin[x] + Cos[y] + 2== 0, {x,y}, Reals]")
# e = wlexpr("Solve[x+0.5 == 0, x, Reals]")
# e2 = wlexpr("Solve[And[x^2 - 2 y^2 == 1,x > 0,y > 0] , {x, y}, Integers]")




def nnDiff(e, vs):
    varsAndRanges = list(zip(*vs))
    variables = varsAndRanges[0]
    # print("variable" + str(variables))
    ranges = varsAndRanges[1]
    # print("ranges" + str(ranges))
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
    # print("conds" + str(conds))
    with WolframLanguageSession() as session:
        session.evaluate("Inv[x_] := 1/x")
        session.evaluate("Neg[x_] := -x")
        f = wlexpr(str(Func(e)))
        wlvs = list(map(wlexpr,variables))
        gradient = session.evaluate(wl.Grad(f, wlvs))
        # print("gradient", gradient)
        for g in gradient:
            g = session.evaluate(wl.FullSimplify(g))
            # print(g)
            eq = wl.Equal(g, 0)
            
            res = session.evaluate(wl.Solve(wl.And([eq] + conds), wlvs, wl.Reals))
            # print(res)
            if (countableManySolution(res)):
                return True
        return False

def countableManySolution(f):
    with WolframLanguageSession() as session:
        if f == ():
            return True
        elif isinstance(f, tuple):
            for r in f:
                # for every rule
                r = r[0]
                if not str(r.head) == "Rule":
                    raise TypeError(r)
                conditionalExpression = r.args[1]
                 #r[0] is variable, r[1] is conditional expression
                if (isinstance(conditionalExpression, numbers.Number)):
                    return True
                elif conditionalExpression.head == "ConditionalExpression":
                    condition = conditionalExpression.args[1]
                    exp = conditionalExpression.args[0]
                    getfreeVars = wlexpr("Reduce`FreeVariables")
                    freeVariables = list(map(str, session.evaluate(getfreeVars(exp))))
                    elems = []
                    if str(condition.head) == "And":
                        elems = list(filter(lambda x: str(x.head) == "Element", condition.args))
                    elif str(condition.head) == "Element":
                        elems = [condition]
                    IntVar = []
                    for elem in elems:
                        if str(elem.args[1]) == "Integers":
                            var = elem.args[0]
                            if str(var.head) == "Alternatives":
                                IntVar.extend(list(map(str, var.args)))
                            else:
                                IntVar.append(str(elem.args[0]))

                    return (all (map (lambda x:str(x) in IntVar, freeVariables)))
            return False
   # 1.empty
   # 2.conditional expression is a number
   # 3.C[n] are integers and No Global Var in Expression
   # condition can be a Element, And of List
if __name__ == "__main__":
    e = ("Times", "x", "x")
    vs = [('x',[(0, "Closed", 1, "Closed"), (10, "Open", 11, "Closed")])]
    print(nnDiff(e, vs))