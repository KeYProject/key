package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.sort.object.InstantiableObjectSort;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that creates term<code>(T[])null</code>
 * where instantiable object sort T is taken from the argument.
 * 
 * @author oleg.myrk@gmail.com
 */
public class UnsizedArraySortMetaOp extends SafeBaseMetaOp {

        public UnsizedArraySortMetaOp() {
                super(new Name("#ClangUnsizedArraySort"), 1);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, 
                        IClangSafeEnvironment context) {
                ISymbolEnv symbolEnv = context.getSymbolEnv(); 
                
                Term term0 = term.sub(0);

                if (!(term0.sort() instanceof IInstantiableObjectSort))
                        throw new RuntimeException(
                                        "#ClangUnsizedArrayType applied to the term that does not have instantiable object sort");

                return TermFactory.DEFAULT.createCastTerm(
                                context.getSafePlatform().getSafeUnsizedArraySort((InstantiableObjectSort)term0.sort()),
                                TermFactory.DEFAULT.createFunctionTerm(symbolEnv.getNullConstant())
                                );
        }
}
