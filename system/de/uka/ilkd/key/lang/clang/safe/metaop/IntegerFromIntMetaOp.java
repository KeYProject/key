package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.metaop.BaseClangMetaOp;
import de.uka.ilkd.key.lang.clang.safe.sort.value.FromIntFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.value.IntegerSort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that applies function <code>T::fromInt</code> to its first
 * argument, whereas sort T is taken from the second argument and must be a CDL
 * integer sort.
 * 
 * @author oleg.myrk@gmail.com
 */
public class IntegerFromIntMetaOp extends BaseClangMetaOp {

        public IntegerFromIntMetaOp() {
                super(new Name("#ClangIntegerFromInt"), 2);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangEnvironment context) {
                Term term0 = term.sub(0);
                Sort sort1 = term.sub(1).sort();
                if (!(sort1 instanceof IntegerSort))
                        throw new RuntimeException(
                                        "#ClangFromInt applied to the second argument of non-integer sort");
                FromIntFunction fromIntFunction = ((IntegerSort) sort1)
                                .getFromIntFunction();
                if (fromIntFunction.argSort(0) != term0.sort())
                        throw new RuntimeException(
                                        "#ClangFromInt applied to the first argument of non-int sort");

                return TermFactory.DEFAULT.createFunctionTerm(fromIntFunction,
                                term0);
        }
}
