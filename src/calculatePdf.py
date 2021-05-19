from wolframclient.evaluation.kernel.localsession import WolframLanguageSession
from nnDiff import Func, sys




if __name__ == "__main__":
    exp = Func(sys.argv[1:])
    #exp = Func(["D", "x", "x"])
    with WolframLanguageSession() as session:
        session.evaluate("Inv[zzz_] := 1/zzz")
        res = session.evaluate(str(exp))        
        print(res)

