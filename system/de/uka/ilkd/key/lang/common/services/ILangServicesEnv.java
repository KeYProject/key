package de.uka.ilkd.key.lang.common.services;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;

/**
 * Environment for the language services.
 *  
 * @author oleg.myrk@gmail.com
 */
public interface ILangServicesEnv  {
        
        /**
         * Returns the symbol environment.
         * @param sortNS
         * @param symbolNS
         * @return
         */
        ISymbolEnv getSymbolEnv(Namespace sortNS, Namespace symbolNS);
                
        /***
         * Formats variable name.
         *  
         * @param name
         * @return
         */
        Name formatVariableName(String name);
        
        /**
         * Returns the main services (non-language specific).
         * 
         * @return
         */
        public IMainServices getMainServices();        
}
