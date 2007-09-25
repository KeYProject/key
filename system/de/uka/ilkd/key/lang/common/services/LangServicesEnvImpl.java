package de.uka.ilkd.key.lang.common.services;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.VariableNamer;

/**
 * A standard implementation of language services.
 * 
 * @author oleg.myrk@gmail.com
 */
public class LangServicesEnvImpl implements ILangServicesEnv {
        private IMainServices mainServices;
        
        /**
         * @inheritDocs
         */
        public LangServicesEnvImpl(IMainServices mainServices) {
                this.mainServices = mainServices;
        }
        
        /**
         * @inheritDocs
         */
        public IMainServices getMainServices() {
                return mainServices;
        }
        
        /**
         * @inheritDocs
         */
        public ISymbolEnv getSymbolEnv(Namespace sortNS, Namespace symbolNS) {
                return new SymbolEnvImpl(sortNS, symbolNS);
        }
        
        /**
         * @inheritDocs
         */
        public Name formatVariableName(String name) {
                return VariableNamer.parseName(name);
        }

}