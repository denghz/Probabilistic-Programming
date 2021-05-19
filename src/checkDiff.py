from wolframclient.evaluation.kernel.localsession import WolframLanguageSession
from nnDiff import Func, sys




if __name__ == "__main__":
    
    file = open('src/checkDiff.nb', 'r').read()
    args = sys.argv[1:]
    exp = None
    if args == []:
        exp = Func(["D", "x", "x"])
    else:
        exp = Func(args)
    with WolframLanguageSession() as session:
        session.evaluate("Inv[zzz_] := 1/zzz")
        session.evaluate("f[" + str(exp.arg2) + "_] = " + str(exp.arg1))
        
        res = session.evaluate(file)
        print(res, file=sys.stderr)

