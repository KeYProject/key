package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ScalarSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ValueLocation;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that applies function <code>T::value</code> to its argument
 * of CDL scalar sort T.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ValueAccessMetaOp extends SafeBaseMetaOp {

        public ValueAccessMetaOp() {
                super(new Name("#ClangValueAccess"), 1);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                Term term0 = term.sub(0);
                if (!(term0.sort() instanceof IScalarSort))
                        throw new RuntimeException(
                                        "#ClangValueAccess applied to a term of non-scalar sort");
                ValueLocation valueLocation = ((ScalarSort) term0.sort())
                                .getValueLocation();

                return TermFactory.DEFAULT.createFunctionTerm(valueLocation,
                                term0);
        }
}
