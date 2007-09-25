package de.uka.ilkd.key.lang.clang.common.iface;

import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Namespace;

/**
 * C langauge specific services.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IClangServices extends ILangServices {
        /**
         * Returns C language environment encapsulating given sort and symbol
         * namespaces.
         * 
         * @param sortNS
         * @param symbolNS
         * @return
         */
        IClangEnvironment getEnvironment(Namespace sortNS, Namespace symbolNS);
}
