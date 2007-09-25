package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.sort.value.IntegerSort;
import de.uka.ilkd.key.lang.clang.safe.sort.value.ToIntFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that applies function <code>T::toInt</code> to its argument
 * of CDL integer sort T.
 * 
 * @author oleg.myrk@gmail.com
 */
public class IntegerToIntMetaOp extends SafeBaseMetaOp {

        public IntegerToIntMetaOp() {
                super(new Name("#ClangIntegerToInt"), 1);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                Term term0 = term.sub(0);
                if (!(term0.sort() instanceof IntegerSort))
                        throw new RuntimeException(
                                        "#ClangToInt applied to a term of non-integer sort");
                ToIntFunction toIntFunction = ((IntegerSort) term0.sort())
                                .getToIntFunction();

                return TermFactory.DEFAULT.createFunctionTerm(toIntFunction,
                                term0);
        }
}
