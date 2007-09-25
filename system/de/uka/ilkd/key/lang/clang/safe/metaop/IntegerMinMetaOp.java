package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.sort.value.IntegerSort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that creates <code>T::MIN</code> constant when applied to an argument of 
 * CDL integer sort T.
 * 
 * @author oleg.myrk@gmail.com
 */
public class IntegerMinMetaOp extends SafeBaseMetaOp {

        public IntegerMinMetaOp() {
                super(new Name("#ClangIntegerMin"), 1);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                Sort sort = term.sub(0).sort();
                if (!(sort instanceof IntegerSort))
                        throw new RuntimeException(
                                        "#ClangIntegerMin applied to a term of non-integer sort");

                return TermFactory.DEFAULT
                                .createFunctionTerm(((IntegerSort) sort)
                                                .getMinConstant());
        }
}
