package de.uka.ilkd.key.lang.clang.safe.metaop.heap;

import java.math.BigInteger;

import de.uka.ilkd.key.lang.clang.common.sort.object.IArraySort;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.metaop.SafeBaseMetaOp;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Op;

/**
 * Meta operation that tries to evaluate expression
 * <code>size(a)</code>, where <code>a</code> is of sized array type.  
 * 
 * @author oleg.myrk@gmail.com
 */
public class TrySizedArraySizeMetaOp extends SafeBaseMetaOp {

        public TrySizedArraySizeMetaOp() {
                super(new Name("#ClangTrySizedArraySize"), 1);
        }

        /**
         * @inheritDocs
         */
        protected Term calculate(Term term, 
                        IClangSafeEnvironment context) {
                ISymbolEnv symbolEnv = context.getSymbolEnv();
                
                if (!(term.sub(0).op() instanceof Function && term.sub(0).op()
                                .name().toString().equals("size")))
                        throw new IllegalArgumentException(
                                        "#TrySizedArraySize first argument must be 'size' function");

                Term arraySizeTerm = term.sub(0);
                Term arrayTerm = arraySizeTerm.sub(0);

                if (arrayTerm.sort() instanceof IArraySort) {
                        BigInteger arraySize = ((IArraySort) arrayTerm
                                        .sort()).getSize();
                        Term notNullTerm = TermFactory.DEFAULT
                                        .createJunctorTerm(
                                                        Op.NOT,
                                                        TermFactory.DEFAULT
                                                                        .createEqualityTerm(
                                                                                        arrayTerm,
                                                                                        TermFactory.DEFAULT
                                                                                                        .createFunctionTerm(symbolEnv
                                                                                                                        .getNullConstant())));
                        TermFactory.DEFAULT.createIfThenElseTerm(notNullTerm,
                                        symbolEnv.encodeInteger(
                                                        arraySize),
                                        symbolEnv.encodeInteger(
                                                        BigInteger.ZERO));
                }

                return arraySizeTerm;
        }
}
