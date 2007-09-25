package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.sort.IClangObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.IClangValueSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafePlatform;
import de.uka.ilkd.key.lang.clang.safe.sort.object.HashMapFromStringToMemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.IteratorOfMemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ScalarSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.StructSort;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Meta operation that creates a conjunction of conditions
 * <code>isValidVal(T::value(c))</code> or
 * <code>isValidPtr(T::value(c))</code> for all leafs <code>c</code> of a
 * term with a struct sort.
 * 
 * @author oleg.myrk@gmail.com
 */
public class DeepIsValidValueMetaOp extends SafeBaseMetaOp {

        public DeepIsValidValueMetaOp() {
                super(new Name("#ClangDeepIsValidValue"), 1);
        }

        /**
         * @inheritDocs
         */
        public Sort sort(Term[] term) {
                return Sort.FORMULA;
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, 
                        IClangSafeEnvironment context) {
                Term term0 = term.sub(0);
                if (!(term0.sort() instanceof StructSort))
                        throw new RuntimeException(
                                        "#ClangDeepIsValidVal should be applied to a terms of a struct sort");
                StructSort structSort = ((StructSort) term0.sort());

                Term result = buildTest(structSort, term0, context);
                return result != null ? result : TermFactory.DEFAULT
                                .createJunctorTerm(Op.TRUE);
        }

        private Term buildTest(StructSort structSort, Term term,
                        IClangSafeEnvironment context) {
                ISymbolEnv symbolEnv = context.getSymbolEnv();
                IClangSafePlatform platform = context.getSafePlatform();
                
                HashMapFromStringToMemberFunction memberFunctionMap = structSort
                                .getMemberFunctionMap();

                Term result = null;

                for (IteratorOfMemberFunction i = memberFunctionMap.values(); i
                                .hasNext();) {
                        MemberFunction memberFunction = (MemberFunction) i
                                        .next();

                        Term childTerm = TermFactory.DEFAULT
                                        .createFunctionTerm(memberFunction,
                                                        term);
                        Sort memberSort = memberFunction.sort();

                        Term testTerm = null;

                        if (memberSort instanceof IScalarSort) {
                                Term valueTerm = TermFactory.DEFAULT
                                                .createFunctionTerm(
                                                                ((ScalarSort) memberSort)
                                                                                .getValueLocation(),
                                                                childTerm);
                                Sort valueSort = valueTerm.sort();

                                if (valueSort instanceof IClangValueSort)
                                        testTerm = TermFactory.DEFAULT
                                                        .createFunctionTerm(
                                                                        platform
                                                                                        .getSafeValueMarkerSort()
                                                                                        .getIsValidValPredicate(),
                                                                        valueTerm);
                                else if (valueSort instanceof IClangObjectSort)
                                        testTerm = TermFactory.DEFAULT
                                                        .createFunctionTerm(
                                                                        platform
                                                                                        .getSafeObjectMarkerSort()
                                                                                        .getIsValidPtrPredicate(),
                                                                        valueTerm);
                                else
                                        assert false;
                        } else if (memberSort instanceof StructSort)
                                testTerm = buildTest((StructSort) structSort,
                                                childTerm, context);
                        else
                                assert (false);

                        if (testTerm != null) {
                                if (result != null)
                                        result = TermFactory.DEFAULT
                                                        .createJunctorTerm(
                                                                        Op.AND,
                                                                        result,
                                                                        testTerm);
                                else
                                        result = testTerm;
                        }
                }

                return result;
        }
}
