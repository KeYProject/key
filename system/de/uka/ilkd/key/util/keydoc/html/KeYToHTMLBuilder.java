package de.uka.ilkd.key.util.keydoc.html;

import java.io.*;


/** The abstract builder class.
 */
abstract class KeYToHTMLBuilder {
	
    /** Every builder must be able to build the HTML representation of a key documentation.
	@param toBuild .key file, for which the documentation should be processed
	@return an object of the class type {@link keydoc.BoxedFile}
    */
    protected static BoxedFile buildHTMLFile(File toBuild) {
    	return null;
    }

}
