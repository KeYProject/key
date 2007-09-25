package de.uka.ilkd.key.lang.clang.safe.metaop.heap;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.metaop.BaseClangMetaOp;
import de.uka.ilkd.key.lang.clang.safe.sort.object.UnsizedArraySort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that tries to evaluate expression
 * <code>sized(a)</code>, where <code>a</code> is array repository
 * term.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryArrayRepositorySizeMetaOp extends BaseClangMetaOp {

        public TryArrayRepositorySizeMetaOp() {
                super(new Name("#ClangTryArrayRepositorySize"), 1);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, 
                        IClangEnvironment context) {
                if (!(term.sub(0).op() instanceof Function && term.sub(0).op()
                                .name().toString().equals("size")))
                        throw new IllegalArgumentException(
                                        "#TryArrayRepositorySize first argument must be 'size' function");

                Term arraySizeTerm = term.sub(0);
                Term arrayTerm = arraySizeTerm.sub(0);

                if (arrayTerm.sort() instanceof UnsizedArraySort) {
                        Function repositoryFunction = ((UnsizedArraySort) arrayTerm
                                        .sort()).getRepositoryFunction();
                        if (arrayTerm.op() == repositoryFunction)
                                return arrayTerm.sub(1);
                }

                return arraySizeTerm;
        }
}
