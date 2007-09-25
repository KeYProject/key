package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.metaop.BaseClangMetaOp;
import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.InstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.RepositoryFunction;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that applies function <code>T::<lookup></code> to its argument
 * of int type, while instantiable object sort T is taken from the second argument.
 * 
 * @author oleg.myrk@gmail.com
 */
public class RepositoryAccessMetaOp extends BaseClangMetaOp {

        public RepositoryAccessMetaOp() {
                super(new Name("#ClangRepositoryAccess"), 2);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangEnvironment context) {
                Term term0 = term.sub(0);
                Term term1 = term.sub(1);
                if (!(term1.sort() instanceof IInstantiableObjectSort))
                        throw new RuntimeException(
                                        "#ClangRepositoryAccess applied to the second argument of non-instantiable object sort");
                RepositoryFunction repositoryFunction = ((InstantiableObjectSort) term1.sort()).getRepositoryFunction();
                if (repositoryFunction.argSort(0) != term0.sort())
                        throw new RuntimeException(
                                "#ClangRepositoryAccess applied to the first argument that is not of int type");

                return TermFactory.DEFAULT.createFunctionTerm(repositoryFunction,
                                term0);
        }
}
