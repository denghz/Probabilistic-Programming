from wolframclient.evaluation.kernel.localsession import WolframLanguageSession
from nnDiff import Func, sys, wl, wlexpr



if __name__ == "__main__":
    
    file = open('src/checkRealInverse.nb', 'r').read()
    exp = Func(sys.argv[1:])
    #exp = Func(["Inverse", "Power", "x", "2", "x"])
    with WolframLanguageSession() as session:
        session.evaluate("Inv[zzz_] := 1/zzz")
        session.evaluate(file)
        res = session.evaluate(wl.Global.RealInverse(wlexpr(str(exp.arg1)), wlexpr(str(exp.arg2))))
        if str(res) == "$Failed":
            print("False", file=sys.stderr)
        else:
            print("True", file=sys.stderr)
