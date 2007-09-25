package de.uka.ilkd.key.lang.clang.safe.metaop.heap;

import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.metaop.SafeBaseMetaOp;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ArrayRepositoryFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ElemFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.RepositoryFunction;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Meta operation that tries to evaluate expression <code>isRootObj(o)</code>,
 * where <code>o</code> is of object type. Evaluation is based on removing
 * accessors at the top-level of term <code>o</code>.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryIsRootObjMetaOp extends SafeBaseMetaOp {

        public TryIsRootObjMetaOp() {
                super(new Name("#ClangTryIsRootObj"), 1);
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
                ISymbolEnv symbolEnv = context.getSymbolEnv();
                
                if (!(term.sub(0).op() instanceof Function && term.sub(0).op()
                                .name().toString().equals("isRootObj")))
                        throw new IllegalArgumentException(
                                        "#TryIsRootObj first argument must be 'isRootObj' predicate");

                Term rootObjTerm = term.sub(0);
                Function isRootObjFun = (Function) rootObjTerm.op();
                Term objTerm = rootObjTerm.sub(0);

                if (objTerm.op() instanceof RepositoryFunction)
                        return TermFactory.DEFAULT.createJunctorTerm(Op.TRUE); 

                if (objTerm.op() instanceof ArrayRepositoryFunction)
                        return TermFactory.DEFAULT.createJunctorTerm(Op.TRUE); 

                if (objTerm.op() instanceof MemberFunction) {
                        Term structuredTerm = objTerm.sub(0);
                        return TermFactory.DEFAULT.createFunctionTerm(
                                        isRootObjFun, structuredTerm);
                }

                if (objTerm.op() instanceof ElemFunction) {
                        Term arrayTerm = objTerm.sub(0);
                        return TermFactory.DEFAULT.createFunctionTerm(
                                        isRootObjFun, arrayTerm);
                }

                if (objTerm.op() == symbolEnv.getNullConstant())
                        return TermFactory.DEFAULT.createJunctorTerm(Op.TRUE);

                return rootObjTerm;
        }
}
