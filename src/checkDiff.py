from wolframclient.evaluation.kernel.localsession import WolframLanguageSession
from nnDiff import Func, sys




if __name__ == "__main__":
    
    file = open('src/checkDiff.nb', 'r').read()
    
    exp = Func(sys.argv[1:])
    #exp = Func(["D", "x", "x"])
    with WolframLanguageSession() as session:
        session.evaluate("Inv[zzz_] := 1/zzz")
        session.evaluate("f[" + str(exp.arg2) + "_] = " + str(exp.arg1))
        res = session.evaluate(file)
        print(res, file=sys.stderr)

