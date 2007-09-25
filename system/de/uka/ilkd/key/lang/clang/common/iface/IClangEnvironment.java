package de.uka.ilkd.key.lang.clang.common.iface;

import de.uka.ilkd.key.lang.common.services.ILangServicesEnv;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Namespace;

/**
 * C specific language environment that contains:
 * a language services environment,
 * a symbol environment,
 * sort and symbol namespaces,
 * a platform.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IClangEnvironment {
        /**
         * Returns the generic language services environment.
         * 
         * @return
         */
        public ILangServicesEnv getLangServicesEnv();
        
        /**
         * Returns the generic symbol environment.
         * @return
         */
        public ISymbolEnv getSymbolEnv();
        
        /**
         * Returns the sort namespaces.
         * @return
         */
        public Namespace getSortNS();
        
        /**
         * Returns the symbol namespaces.
         * @return
         */
        public Namespace getSymbolNS();


        /**
         * Returns current C platform.
         * @return
         */
        public IClangPlatform getPlatform();
}