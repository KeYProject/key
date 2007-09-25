package de.uka.ilkd.key.util.keydoc.html;

import java.io.File;

/** Class containing the HTML representation of the .Key files documentation as processed by the KeyToHTMLBuilder and some other usefull information for the Director.
    It stores the three attributes fileName, shortDescription and the processed html file.
 */
class BoxedFile {
    private File file;
    private int firstLength;
    private int firstOffset;
    private HTMLFile htmlFile;

    /** Boxedfile Constructor.
     * Boxes a HTMLFile 
     * @param fileName The name of the .key file
     * @param shortDescription Short description of the purpose of the .key file
     * @param htmlFile The processed .key file
     */
    public BoxedFile(File file, int firstLength, int firstOffset, HTMLFile htmlFile) {
    	this.file= file;
    	this.firstLength= firstLength;
    	this.firstOffset= firstOffset;
    	this.htmlFile= htmlFile;
    }

    protected File getFile() {
    	return file;
    }

    protected int getFirstOffset() {
    	return firstOffset;
    }

    protected HTMLFile getHtmlFile() {
    	return htmlFile;
    }
    
    protected int getFirstLength() {
    	return firstLength;
    }
}
















