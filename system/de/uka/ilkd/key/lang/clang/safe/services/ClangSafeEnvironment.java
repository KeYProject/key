package de.uka.ilkd.key.lang.clang.safe.services;

import de.uka.ilkd.key.lang.clang.common.iface.IClangPlatform;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafeEnvironment;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafePlatform;
import de.uka.ilkd.key.lang.common.services.ILangServicesEnv;
import de.uka.ilkd.key.lang.common.services.ISymbolEnv;
import de.uka.ilkd.key.logic.Namespace;

/**
 * Safe CDL environment implemenation.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ClangSafeEnvironment implements IClangSafeEnvironment {
        private ILangServicesEnv langServicesEnv;
        private Namespace sortNS;
        private Namespace symbolNS;
        private IClangSafePlatform platform;
        
        public ClangSafeEnvironment(ILangServicesEnv langServicesEnv, Namespace sortNS, Namespace symbolNS, IClangSafePlatform platform) {
                this.langServicesEnv = langServicesEnv;
                this.sortNS = sortNS;
                this.symbolNS = symbolNS;
                this.platform = platform;
        }
        
        public ILangServicesEnv getLangServicesEnv() {
                return langServicesEnv;
        }

        public ISymbolEnv getSymbolEnv() {
                return langServicesEnv.getSymbolEnv(sortNS, symbolNS);
        }
        
        public Namespace getSortNS() {
                return sortNS;
        }
        
        public Namespace getSymbolNS() {
                return symbolNS;
        }
        
        public IClangPlatform getPlatform() {
                return platform;
        }
        
        public IClangSafePlatform getSafePlatform() {
                return platform;
        }        
}
