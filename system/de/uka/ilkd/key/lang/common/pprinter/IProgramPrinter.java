package de.uka.ilkd.key.lang.common.pprinter;

import java.io.Writer;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * An interface for printing program elements.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IProgramPrinter {
        /**
         * Initializes the program printer with a writer to print to.
         * Can be called multiple times.
         * 
         * @param writer
         */
        void init(Writer writer);        

        /**
         * Sets wheter to print line-feeds.
         * @param noLinefeed
         */
        void setNoLineFeed(boolean noLinefeed);
        
        /**
         * Sets the indentation level --- the number of blanks (#32)
         * at the beginning of each line.
         * 
         * @param noLinefeed
         */
        void setIndentationLevel(int level);
        
        /**
         * Prints the program element to the writer. 
         * @param pe
         * @throws java.io.IOException
         */
        void print(IProgramElement pe) throws java.io.IOException;
        
        /**
         * Returns the (line,column)-range of the focus, typically
         * the first active statement.
         * 
         * @return
         */
        Range getFocusRange();        
}
