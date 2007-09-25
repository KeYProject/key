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
 * Meta operation that tries to evaluate expression <code>isValidObj(o)</code>, 
 * where <code>o</code> is of object type. Evaluation is based on removing accessors
 * at the top-level of term <code>o</code>. The second auxiliary argument must be
 * <code>isRealObj(null)</code>. The third auxiliary argument must be
 * <code>isValildIdx(null, 0)</code>
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryIsValidObjMetaOp extends SafeBaseMetaOp {

        public TryIsValidObjMetaOp() {
                super(new Name("#ClangTryIsValidObj"), 3);
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
                
                if (!(term.sub(0).op() instanceof Function && term.sub(0).op().name().toString().equals("isValidObj")))
                        throw new IllegalArgumentException("#TryIsValidObj first argument must be 'isValidObj' predicate");
                
                if (!(term.sub(1).op() instanceof Function && term.sub(1).op().name().toString().equals("isRealObj")))
                        throw new IllegalArgumentException("#TryIsValidObj second argument must be 'isRealObj' predicate");
                
                if (!(term.sub(2).op() instanceof Function && term.sub(2).op().name().toString().equals("isValidIdx")))
                        throw new IllegalArgumentException("#TryIsValidObj third argument must be 'isValidIdx' predicate");

                Term isValidObjTerm = term.sub(0);
                Function isRealObjFun = (Function)term.sub(1).op();
                Function isValidIdxFun = (Function)term.sub(2).op();
                
                Term objTerm = isValidObjTerm.sub(0);
                
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
                        Term indexIsValid = TermFactory.DEFAULT.createFunctionTerm(isValidIdxFun, new Term[] { arrayTerm, arrayIndexTerm} );
 
                        return TermFactory.DEFAULT.createJunctorTerm(Op.AND, new Term[] {parentIsRealObj, indexIsValid});
                }
                
                if (objTerm.op() == symbolEnv.getNullConstant())
                        return TermFactory.DEFAULT.createJunctorTerm(Op.FALSE);
                
                return isValidObjTerm;
        }
}
