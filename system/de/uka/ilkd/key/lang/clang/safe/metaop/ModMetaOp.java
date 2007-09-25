package de.uka.ilkd.key.lang.clang.safe.metaop;

import java.math.BigInteger;

import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that computes division remainder of two integer literals.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ModMetaOp extends SafeBaseMetaOp {

        public ModMetaOp() {
                super(new Name("#ClangMod"), 2);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                ISymbolEnv symbolEnv = context.getSymbolEnv();
                
                Term term0 = term.sub(0);
                Term term1 = term.sub(1);
                
                BigInteger arg1 = symbolEnv.parseInteger(term0);
                BigInteger arg2 = symbolEnv.parseInteger(term1);

                // If division by zero
                if (arg2.equals(BigInteger.valueOf(0))) {
                    Name undefName = new Name("undef("+term+")");
                    Function undef = (Function)context.getSymbolNS().lookup(undefName);
                    if (undef==null) {
                        undef = new RigidFunction(undefName,
                                             symbolEnv.getIntSort(), 
                                             new Sort[0]);
                        context.getSymbolNS().add(undef);
                    }
                    return TermFactory.DEFAULT.createFunctionTerm(undef);
                }
                
                BigInteger result = arg1.remainder(arg2);
                return symbolEnv.encodeInteger(result);        
        }
}
