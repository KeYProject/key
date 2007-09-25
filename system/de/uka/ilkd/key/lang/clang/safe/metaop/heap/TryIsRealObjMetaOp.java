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
 * Meta operation that tries to evaluate expression <code>isRealObj(o)</code>, 
 * where <code>o</code> is of object type. Evaluation is based on removing accessors
 * at the top-level of term <code>o</code>. The second auxiliary argument must be
 * <code>isRealIdx(null, 0)</code>
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryIsRealObjMetaOp extends SafeBaseMetaOp {

        public TryIsRealObjMetaOp() {
                super(new Name("#ClangTryIsRealObj"), 2);
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
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                ISymbolEnv symbolEnv = context.getSymbolEnv();
                
                if (!(term.sub(0).op() instanceof Function && term.sub(0).op().name().toString().equals("isRealObj")))
                        throw new IllegalArgumentException("#TryIsRealObj first argument must be 'isRealObj' predicate");
                
                if (!(term.sub(1).op() instanceof Function && term.sub(1).op().name().toString().equals("isRealIdx")))
                        throw new IllegalArgumentException("#TryIsRealObj third argument must be 'isRealIdx' predicate");

                Term isRealObjTerm = term.sub(0);
                Function isRealObjFun = (Function)isRealObjTerm.op();
                Function isRealIdxFun = (Function)term.sub(1).op();
                
                Term objTerm = isRealObjTerm.sub(0);
                
                if (objTerm.op() instanceof RepositoryFunction)
                        return TermFactory.DEFAULT.createJunctorTerm(Op.TRUE); 

                if (objTerm.op() instanceof ArrayRepositoryFunction)
                        return TermFactory.DEFAULT.createJunctorTerm(Op.TRUE); 

                if (objTerm.op() instanceof MemberFunction) {
                        Term structuredTerm = objTerm.sub(0); 
                        return TermFactory.DEFAULT.createFunctionTerm(isRealObjFun, structuredTerm);
                }
                
                if (objTerm.op() instanceof ElemFunction) {
                        Term arrayTerm = objTerm.sub(0);
                        Term arrayIndexTerm = objTerm.sub(1);
                        
                        Term parentIsRealObj = TermFactory.DEFAULT.createFunctionTerm(isRealObjFun, arrayTerm);
                        Term indexIsReal = TermFactory.DEFAULT.createFunctionTerm(isRealIdxFun, new Term[] { arrayTerm, arrayIndexTerm} );
 
                        return TermFactory.DEFAULT.createJunctorTerm(Op.AND, new Term[] {parentIsRealObj, indexIsReal});
                }
                
                if (objTerm.op() == symbolEnv.getNullConstant())
                        return TermFactory.DEFAULT.createJunctorTerm(Op.FALSE);
                
                return isRealObjTerm;
        }
}
