package de.uka.ilkd.key.lang.clang.safe.sort;

/**
 * Assorted CDL sort utilities.
 * @author oleg.myrk@gmail.com
 */
public class SortUtil {

        /**
         * Escapes C identifier so that the result contains only
         * standard identifier characters [a-z]|[A-Z]|[0-9][_] and
         * escapes all other characters into the form "%N" wherer N
         * is the unicode code of the character.
         * 
         * @param id
         * @return
         */
        public static String escapeCIdentifier(String id) {
                StringBuffer result = new StringBuffer();
                for(int i = 0; i < id.length(); i++) {
                        char c = id.charAt(i);
                        if ('a' <= c && c <= 'z')
                                result.append(c);
                        else if ('A' <= c && c <= 'Z')
                                result.append(c);
                        else if (c == '_')
                                result.append(c);
                        else if ('0' <= c && c <= '9')
                                result.append(c);
                        else {
                                result.append("%");
                                result.append((int)c);
                        }
                }
                return result.toString();
        }
}
