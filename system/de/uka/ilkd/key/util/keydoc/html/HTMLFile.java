package de.uka.ilkd.key.util.keydoc.html;

/** Class containing the code for the .key files HTML documentation.
 */
class HTMLFile {
    private StringBuffer htmlFile;

    /** Constructor turning a StringBuffer into a HTMLFile representation
     */
    public HTMLFile(StringBuffer htmlFile) {
	this.htmlFile= htmlFile;
    }

    public HTMLFile(String htmlFile) {
	this.htmlFile= new StringBuffer(htmlFile);
    }

    /**
       Returns the String representation of the contained HTML file.
     */
    public String getHTMLFileAsString() {
	return htmlFile.toString();
    }
}
