package de.uka.ilkd.key.lang.clang.safe.metaop.heap;

import java.math.BigInteger;

import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.metaop.SafeBaseMetaOp;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ArrayRepositoryFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ElemFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.MemberFunction;
import de.uka.ilkd.key.lang.clang.safe.sort.object.RepositoryFunction;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Meta operation that tries to evaluate expression <code>objParentIdx(o)</code>, 
 * where <code>o</code> is of object type. Evaluation is based on removing accessors
 * at the top-level of term <code>o</code>.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TryObjParentIdxMetaOp extends SafeBaseMetaOp {

        public TryObjParentIdxMetaOp() {
                super(new Name("#ClangTryObjParentIdx"), 1);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, IClangSafeEnvironment context) {
                ISymbolEnv symbolEnv = context.getSymbolEnv();
                
                if (!(term.sub(0).op() instanceof Function && term.sub(0).op().name().toString().equals("objParentIdx")))
                        throw new IllegalArgumentException("#TryObjParentIdx first argument must be 'objParentIdx' function");

                Term objParentIdxTerm = term.sub(0);
                Term objTerm = objParentIdxTerm.sub(0);

                if (objTerm.op() instanceof MemberFunction) {
                        int index = ((MemberFunction)objTerm.op()).getMemberInfo().getOrder();
                        return symbolEnv.encodeInteger(BigInteger.valueOf(index));
                }
                        
                if (objTerm.op() instanceof ElemFunction) {
                        Term arrayParentIdx = objTerm.sub(1);
                        return arrayParentIdx;
                }
                
                if (objTerm.op() instanceof RepositoryFunction) {
                        return objParentIdxTerm;
                }

                if (objTerm.op() instanceof ArrayRepositoryFunction) {
                        return objParentIdxTerm;
                }
                
                if (objTerm.op() == symbolEnv.getNullConstant())
                        return objParentIdxTerm;
                
                return objParentIdxTerm;
        }
}
