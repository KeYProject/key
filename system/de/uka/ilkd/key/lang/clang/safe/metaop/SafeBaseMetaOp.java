package de.uka.ilkd.key.lang.clang.safe.metaop;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.metaop.BaseClangMetaOp;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;

/**
 * Base implementation of meta operator for C language.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class SafeBaseMetaOp extends BaseClangMetaOp {
        public SafeBaseMetaOp(Name name, int arity) {
                super(name, arity);
        }

        protected final Term calculate(Term term, 
                        IClangEnvironment context) {
                return calculate(term, (IClangSafeEnvironment)context);
        }

        /**
         * Calculates the result of applying the meta operation.
         * 
         * @param term
         * @param svInst
         * @param services
         * @param symbolInfo
         * @return
         */
        protected abstract Term calculate(Term term, 
                        IClangSafeEnvironment context);
}