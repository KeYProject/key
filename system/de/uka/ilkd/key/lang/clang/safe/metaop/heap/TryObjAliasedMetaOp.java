package de.uka.ilkd.key.lang.clang.safe.metaop.heap;

import java.math.BigInteger;

import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.metaop.SafeBaseMetaOp;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ArrayRepositoryFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ElemFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.RepositoryFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.StructSort;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Meta operation that tries to evaluate expression <code>objAliased(o1, o2)</code>, 
 * where <code>o1, o2</code> are of object type. Evaluation is based on removing 
 * accessors at the top-level of terms.
 * 
 * NB! Doesn't work with unions!
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryObjAliasedMetaOp extends SafeBaseMetaOp {

        public TryObjAliasedMetaOp() {
                super(new Name("#ClangTryObjAliased"), 1);
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
                
                if (!(term.sub(0).op() instanceof Function && term.sub(0).op().name().toString().equals("objAliased")))
                        throw new IllegalArgumentException("#TryObjAliased first argument must be 'objAliased' predicate");

                Term objAliasedTerm = term.sub(0);
                Function objAliasedFun = (Function)objAliasedTerm.op();
                Term objTerm0 = objAliasedTerm.sub(0);
                Term objTerm1 = objAliasedTerm.sub(1);
                
                Term objEqTerm = TermFactory.DEFAULT.createEqualityTerm(new Term[] { objTerm0, objTerm1 } );
                
                if (objTerm1.op() instanceof RepositoryFunction)
                        return objEqTerm;
                
                if (objTerm1.op()  instanceof ArrayRepositoryFunction)
                        return objEqTerm; 
                
                if (objTerm1.op() == symbolEnv.getNullConstant())
                        return objEqTerm;                

                if (objTerm1.op() instanceof MemberFunction && ((MemberFunction)objTerm1.op()).getStructuredSort() instanceof StructSort) {
                        // Must be the first member
                        if (((MemberFunction)objTerm1.op()).getMemberInfo().getOrder() != 0) 
                                return TermFactory.DEFAULT.createJunctorTerm(Op.FALSE);
                        
                        Term structuredTerm = objTerm1.sub(0);
                        Term parentAliasedTerm = TermFactory.DEFAULT.createFunctionTerm(objAliasedFun, new Term[] { objTerm0, structuredTerm } );
                        
                        return TermFactory.DEFAULT.createJunctorTerm(Op.OR, new Term[] { objEqTerm, parentAliasedTerm });
                }
                        
                if (objTerm1.op() instanceof ElemFunction) {
                        Term arrayTerm = objTerm1.sub(0);
                        Term arrayIndexTerm = objTerm1.sub(1);

                        Term indexIsZero = TermFactory.DEFAULT.createEqualityTerm(arrayIndexTerm, symbolEnv.encodeInteger(BigInteger.ZERO));
                        Term parentAliasedTerm = TermFactory.DEFAULT.createFunctionTerm(objAliasedFun, new Term[] { objTerm0, arrayTerm } );
                        
                        Term parentAliasedIfFirstTerm = TermFactory.DEFAULT.createJunctorTerm(Op.AND, new Term[] { indexIsZero, parentAliasedTerm }); 
                        
                        return TermFactory.DEFAULT.createJunctorTerm(Op.OR, new Term[] { objEqTerm, parentAliasedIfFirstTerm });
                }
                        
                return objAliasedTerm;
        }
}
