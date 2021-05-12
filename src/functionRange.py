from logging import error
from wolframclient.evaluation import WolframLanguageSession
from wolframclient.language import wl, wlexpr
from wolframclient.deserializers import WXFConsumer, binary_deserialize
from wolframclient.serializers import export, wolfram_encoder
import wolframclient
import sys



class InEqConsumer(WXFConsumer):
    ineq = wl.Inequality
    lessEq = wl.LessEqual
    less = wl.Less
    gtEq = wl.GreaterEqual
    gt = wl.Greater
    eq = wl.Equal
    def build_function(self, head, args, **kwargs):
        with WolframLanguageSession() as session:
            def f1(x):
                return session.evaluate(wl.N(x))
            f2 = lambda x:'Closed' if x == self.lessEq else 'Open'
            if head == self.ineq and len(args) == 5:
                lb = f1(args[0])
                lbt = f2(args[1])
                ub = f1(args[-1])
                ubt = f2(args[-2])
                return ((lb,lbt), (ub,ubt))
            elif head == self.lessEq or head == self.less:
                if len(args) == 3:
                    lb = f1(args[0])
                    ub = f1(args[-1])
                    lbt = ubt = 'Closed' if head == self.lessEq else 'Open'
                    return ((lb,lbt), (ub,ubt))
                elif len(args) == 2:
                    if isinstance(args[0], wolframclient.language.expression.WLSymbol):
                        b = f1(args[1])
                        bt = 'Closed' if head == self.lessEq else 'Open'
                        return (None, (b,bt))
                    else:
                        b = f1(args[0])
                        bt = 'Closed' if head == self.lessEq else 'Open'
                        return ((b,bt), None)
                else:
                    return super().build_function(head, args, **kwargs)
            elif head == self.gtEq or head == self.gt:
                if len(args) == 3:
                    ub = f1(args[0])
                    lb = f1(args[-1])
                    lbt = ubt = 'Closed' if head == self.lessEq else 'Open'
                    return ((lb,lbt), (ub,ubt))
                elif len(args) == 2:
                    if isinstance(args[1], wolframclient.language.expression.WLSymbol):
                        b = f1(args[0])
                        bt = 'Closed' if head == self.lessEq else 'Open' 
                        return (None, (b,bt))
                    else:
                        b = f1(args[1])
                        bt = 'Closed' if head == self.lessEq else 'Open' 
                        return ((b,bt), None)
                else:
                    return super().build_function(head, args, **kwargs)
            elif head == self.eq and len(args) == 2:
                b = None
                if isinstance(args[0], wolframclient.language.expression.WLSymbol):
                    b = f1(args[1])
                else:
                    b = f1(args[0])
                return ((b, 'Closed'), (b, 'Closed'))
            else:
                return super().build_function(head, args, **kwargs)
            
def calRange(f, lb, lbt, ub, ubt):
    with WolframLanguageSession() as session:
        f = wlexpr(f)
        lbt = '<' if lbt == 'Open' else '<='
        ubt = '<' if ubt == 'Open' else '<='
        lb = '-Infinity' if lb == None else str(lb)
        ub = 'Infinity' if ub == None else str(ub)
        ineq = wlexpr(lb+lbt+'x'+ubt+ub)
        expr = wl.FunctionRange([f(wl.x), ineq], wl.x, wl.y)
        wxf = session.evaluate_wxf(expr)
        res = binary_deserialize(wxf, consumer=InEqConsumer())
        session.terminate()
        return res

if __name__ == "__main__":
    args = sys.argv[1:]
    if len(args) != 5:
        print("wrong number of args")
    else:
        f = args[0]
        lb = None if args[1] == "Nothing" else float(args[1]) 
        lbt = args[2]
        ub =  None if args[3] == "Nothing" else float(args[3]) 
        ubt = args[4]
        for e in calRange(f, lb, lbt, ub,ubt):
            print(e[0], file=sys.stderr)
            print(e[1], file=sys.stderr)
    # print(calRange("Sin", 0, "Closed", 0, "Closed"))