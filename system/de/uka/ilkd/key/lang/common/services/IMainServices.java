package de.uka.ilkd.key.lang.common.services;

/**
 * The interface of the main (non-language specific) services.
 * @author oleg.myrk@gmail.com
 */
public interface IMainServices {
        /**
         * Returns the language services, may be <code>null</code>.
         * @return
         */
        public ILangServices getLangServices();
}
