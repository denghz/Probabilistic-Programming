from wolframclient.language.expression import WLSymbol
from nnDiff import *
    
def parseGlobalSymbol(s):
    if isinstance(s, numbers.Number):
        return s
    if isinstance(s, WLSymbol):
        if s.name == 'E':
            return 'E'
        else:
            return s.name[7:]
    
def parse(exp):
    symbol = parseGlobalSymbol(exp)
    if symbol:
        return [symbol]
    else:
        f = str(exp.head)
        args = list(map(parse, exp.args))
        res = []
        if (f == "Power"):
            res1 = []
            p = args[1][0]
            
            e = args[0]
            
            if e == ['E']:
                return ['Exp'] + args[1]
            if p < 0:
                res = ["Inv"]
                p = -p
            if p >= 2:
                p = p - 2
                res1 = ["Times"] + e + e
                while p > 0:
                    p = p - 1
                    res1 = ["Times"] + res1 + e
                return res + res1
            else:
                return res + e
        else:
            if len(args) == 1:
                return [f] + args[0]
            elif len(args) >= 2:
                res = [f] + args[0] + args[1]
                args = args[2:]
                for arg in args:
                    res = [f] + res + arg
            return res

def simplify(exp):
    with WolframLanguageSession() as session:
        session.evaluate("Inv[zzz_] := 1/zzz")
        f = wlexpr(str(Func(exp)))
        getfreeVars = wlexpr("Reduce`FreeVariables")
        freeVariables = session.evaluate(getfreeVars(f))
        ass =  wl.Element(wl.Alternatives(freeVariables), wl.Reals)
        wmres = session.evaluate(wl.FullSimplify(f,ass))
        print(wmres)
        res = parse(wmres)
        return res



if __name__ == "__main__":
    
    exp = sys.argv[1:]
    
    if exp == []:
        exp = ["Sin", "x"]
    res = map(str,simplify(exp))
    print(' '.join(res), file=sys.stderr) 