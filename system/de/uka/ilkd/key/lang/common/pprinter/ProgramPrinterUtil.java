package de.uka.ilkd.key.lang.common.pprinter;

import java.io.IOException;
import java.io.StringWriter;

import de.uka.ilkd.key.lang.common.program.IProgramElement;

/**
 * Utility class for program printing.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ProgramPrinterUtil {
        /**
         * Formats a program element into a string.
         * @param programElement
         * @return
         * @throws IOException
         */
        public static String formatProgramElement(
                        IProgramElement programElement)
                        throws IOException {
                StringWriter sw = new StringWriter();
                IProgramPrinter pp = programElement.createDefaultPrinter();
                pp.init(sw);
                pp.print(programElement);
                return sw.toString();
        }

        /**
         * Formats a program element into a string without line-feeds.
         * @param programElement
         * @return
         * @throws IOException
         */
        public static String formatProgramElementNoLF(
                        IProgramElement programElement)
                        throws IOException {
                StringWriter sw = new StringWriter();
                IProgramPrinter pp = programElement.createDefaultPrinter();
                pp.init(sw);
                pp.setNoLineFeed(true);
                pp.print(programElement);
                return sw.toString();
        }
}
