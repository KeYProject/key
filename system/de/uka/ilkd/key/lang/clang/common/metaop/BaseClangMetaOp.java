package de.uka.ilkd.key.lang.clang.common.metaop;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.iface.IClangServices;
import de.uka.ilkd.key.lang.common.metaop.BaseMetaOp;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;

/**
 * Base implementation of meta operator for C language.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseClangMetaOp extends BaseMetaOp {
        public BaseClangMetaOp(Name name, int arity) {
                super(name, arity);
        }

        /**
         * @inheritDocs
         */
        public final Term calculate(Term term, 
                        ILangServices services, Namespace sortNS, Namespace symbolNS) {
                return calculate(term, ((IClangServices) services)
                                .getEnvironment(sortNS, symbolNS));
        }

        /**
         * Calculates the result of applying the meta operation.
         * 
         * @param term
         * @param services
         * @param symbolInfo
         * @return
         */
        protected abstract Term calculate(Term term, 
                        IClangEnvironment context);
}