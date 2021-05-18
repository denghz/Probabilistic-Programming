import sys
from wolframclient.evaluation import WolframLanguageSession
from wolframclient.language import wl, wlexpr
from wolframclient.deserializers import WXFConsumer, binary_deserialize
from wolframclient.serializers import export, wolfram_encoder
import wolframclient
import numbers
import itertools

functions1 = ("Sin", "Cos", "Tan", "Exp", "Log", "Minus", "Inv")
functions2 = ("Plus", "Subtract", "Times", "Integrate", "D", "Function", "Power", "Inverse")
functions4 = ("IntegrateBound", )
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
        if self.name in functions4:
            self.name = "Integrate"
            self.arg1 = Func(pn)
            self.arg2 = [Func(pn)]
            self.arg2.append(Func(pn))
            self.arg2.append(Func(pn))
    def __str__(self):
        if self.arg1 == None and self.arg2 == None:
            return self.name
        return self.name + "[" + str(self.arg1) + (", " + (str(self.arg2)) if self.arg2 is not None else "") + "]" 


#falseEmp = wlexpr("Sin[x] + Cos[y] == 0")
# trueEmp = wlexpr("Solve[Sin[x] + Cos[y] + 2== 0, {x,y}, Reals]")
# e = wlexpr("Solve[x+0.5 == 0, x, Reals]")
# e2 = wlexpr("Solve[And[x^2 - 2 y^2 == 1,x > 0,y > 0] , {x, y}, Integers]")




def nnDiff(e, vs):
    variables = list(map(lambda x:x[0], vs))
    print("variable " + str(variables))
    ranges = list(map(lambda x:x[1:], vs))
    def chunks4(lst):
        for i in range(0, len(lst), 4):
            yield tuple(lst[i:i + 4])
    ranges = list(map(lambda x: list(chunks4(x)), ranges))
    print("ranges " + str(ranges))
    def rangeToWlexpr(var, lb, lbt, ub, ubt):
        lbt = '<' if lbt == 'Open' else '<='
        ubt = '<' if ubt == 'Open' else '<='
        lb = '-Infinity' if lb == "Nothing" else str(lb)
        ub = 'Infinity' if ub == "Nothing" else str(ub)
        return wlexpr(lb+lbt+var+ubt+ub)
    conds = []
    for i in range(len(variables)):
        var = variables[i]
        res = list(map(lambda r:rangeToWlexpr(var, *r), ranges[i]))
        if res != []:
            conds.append(wl.Or(*res))
    
    with WolframLanguageSession() as session:
        session.evaluate("Inv[zzz_] := 1/zzz")
        f = wlexpr(str(Func(e)))
        print("input expression " + str(f))
        wlvs = list(map(wlexpr,variables))
        gradient = session.evaluate(wl.Grad(f, wlvs))
        print("gradient ", gradient)
        for g in gradient:
            g = session.evaluate(wl.FullSimplify(g))
            # print(g)
            eq = wl.Equal(g, 0)
            #  
            res = session.evaluate(wl.Solve(wl.And([eq] + conds), wlvs , wl.Reals))
            print("solution of " + str(wl.And([eq] + conds)) + " is " + str(res))
            c = countableManySolution(res, ['x','y'])
            if c:
                return True
        return False

def countableManySolution(f, vs):
    vs = list(map(lambda v:"Global`" + v, vs)) + list(vs)
    with WolframLanguageSession() as session:
        getfreeVars = wlexpr("Reduce`FreeVariables")
        if f == ():
            print(str(f) + " is empty set, then countable")
            return True
        elif isinstance(f, tuple):
            print("try to see if " + str(f) + " is countable")
            for r in f:
                # for every rule
                r = r[0]
                if not str(r.head) == "Rule":
                    raise TypeError(r)
                conditionalExpression = r.args[1]
                 #r[0] is variable, r[1] is conditional expression
                if (isinstance(conditionalExpression, numbers.Number)):
                    print(str(r) + " is a singleton integer, then countable")
                    continue
                elif str(conditionalExpression.head) == "ConditionalExpression":
                    condition = conditionalExpression.args[1]
                    exp = conditionalExpression.args[0]
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
                    if not (all (map (lambda x:str(x) in IntVar or str(x) in vs, freeVariables))):
                        print(str(r) + " is not countable")
                        return False
                    print(str(r) + " is countable")
                    continue
                else:
                    freeVariables = list(map(str, session.evaluate(getfreeVars(conditionalExpression))))
                    if not (all (map (lambda x: str(x) in vs, freeVariables))):
                        print(str(r) + " is not countable")
                        return False
                    print(str(r) + " is countable")
                    continue
            return True
        return False
   # 1.empty
   # 2.conditional expression is a number
   # 3.C[n] are integers and No Global Var in Expression
   # condition can be a Element, And of List
if __name__ == "__main__":
    spl = lambda lst, delim: [list(y) for x, y in itertools.groupby(lst, lambda z: z == delim) if not x]
    args = sys.argv[1:]
    exp = []
    vs = []
    if args == []:
        exp = ["Plus", "Times", "x", "x", "Times", "x", "y"]
        vs = [['x', "0", "Open", "10", "Open"], ['y']]
    else:
        res = spl(args, "||")
        print(res)
        exp = res[0]
        vs = res[1]
        vs = spl(vs, "##")
    print(nnDiff(exp, vs), file =sys.stderr)

