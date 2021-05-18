from wolframclient.evaluation.kernel.localsession import WolframLanguageSession
from nnDiff import Func, sys




if __name__ == "__main__":
    
    
    
    exp = Func(sys.argv[1:])
    #exp = Func(["D", "x", "x"])
    with WolframLanguageSession() as session:
        session.evaluate("Inv[zzz_] := 1/zzz")
        d = "D["+ str(exp.arg1) + ", "+ str(exp.arg1) + "]"
        res = session.evaluate("Reduce[" + d + "<= 0 || " + d + " >= 0 ]")
        print(res, file=sys.stderr)

