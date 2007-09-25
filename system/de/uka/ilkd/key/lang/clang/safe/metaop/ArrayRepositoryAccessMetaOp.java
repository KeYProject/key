package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ArrayRepositoryFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that applies function <code>T[]::<lookup></code> to its 
 * first two arguments of int type, while element sort T is taken 
 * from the thrid argument.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ArrayRepositoryAccessMetaOp extends SafeBaseMetaOp {

        public ArrayRepositoryAccessMetaOp() {
                super(new Name("#ClangArrayRepositoryAccess"), 3);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                Term term0 = term.sub(0);
                Term term1 = term.sub(1);
                Term term2 = term.sub(2);
                if (!(term2.sort() instanceof IInstantiableObjectSort))
                        throw new RuntimeException(
                                        "#ClangArrayRepositoryAccess applied to the third argument of instantiable object sort");
                ArrayRepositoryFunction repositoryFunction = context.getSafePlatform().getSafeUnsizedArraySort((IInstantiableObjectSort) term2.sort()).getRepositoryFunction();
                if (repositoryFunction.argSort(0) != term0.sort() || repositoryFunction.argSort(1) != term1.sort())
                        throw new RuntimeException(
                                "#ClangArrayRepositoryAccess applied to the first or second argument that is not of int type");

                return TermFactory.DEFAULT.createFunctionTerm(repositoryFunction,
                                new Term[]{ term0, term1});
        }
}
