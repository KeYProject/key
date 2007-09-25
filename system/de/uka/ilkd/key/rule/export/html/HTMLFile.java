//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export.html;

import java.io.*;
import java.net.URL;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.zip.GZIPOutputStream;

import de.uka.ilkd.key.rule.export.*;
import de.uka.ilkd.key.util.KeYResourceManager;



public abstract class HTMLFile extends HTMLContainer {
    //  DO NOT CHANGE THE FOLLOWING 2 LINES, UNLESS YOU KNOW ABOUT PRCS-REPLACEMENT
    /* $Format: "    private static final String PRCSVERSION = \"$ProjectVersion$\";"$ */
    private static final String PRCSVERSION = "engelcMemoryConsumption.25";


    
    static KeYResourceManager resManager = KeYResourceManager.getManager();

    public static String getTemplate(String s) {
        //System.out.println("load template: "+s);
        URL templateURL = resManager.getResourceFile(HTMLFile.class, s);
        if (templateURL == null) {
            //System.out.println("could not get resource URL");
            return null;
        }
        //System.out.println("resource URL is:"+templateURL);
        char[] readBuffer = new char[1024];
        StringBuffer textBuffer = new StringBuffer();
        try {
            FileReader reader = new FileReader(templateURL.getFile());
            int read;
            while ((read = reader.read(readBuffer)) > 0) {
                textBuffer.append(readBuffer, 0, read);
            }
        }
        catch (FileNotFoundException e) {
            System.err.println ( "file not found: "+templateURL );
            return null;
        }
        catch (IOException e) {
            System.err.println ( "could not read from file: "+templateURL );
            return null;
        }
        return textBuffer.toString();
    }
    
    private HTMLModel htmlModel;
    private HTMLContainer htmlContainer;
    private String filename;
    private int idCount = 0;
    
    private HashMap fragment2id = new HashMap();
    
    protected RuleExportModel model = null;
    
    public HTMLFile(HTMLModel htmlModel, HTMLContainer htmlContainer, String filename) {
        super(htmlContainer.getRootFolder());
        this.htmlModel = htmlModel;
        this.htmlContainer = htmlContainer;
        this.filename = filename;
        
        htmlContainer.addFile(this);
    }
    
    protected HTMLModel htmlModel() {
        return htmlModel;
    }
    
    protected HTMLContainer htmlContainer() {
        return htmlContainer;
    }
    public String getFilename() {
        return filename;
    }
    
    public String getRelPath ( HTMLFile targetFile ) {
        return htmlModel.getRelPath ( this, targetFile );
    }
    
    public String getNextId() {
        idCount++;
        return "id"+idCount;
    }
    
    public HTMLLink getFileLink(HTMLFile target) {
        return htmlModel.getFileLink(this, target);
    }
    
    public HTMLLink getFragmentLink(Object key) {
        return htmlModel.getFragmentLink(this, key);
    }
    
    public HTMLAnchor getFragmentAnchor ( Object key ) {
        return htmlModel.getFragmentAnchor(this, key);
    }
    
    public void addFragment(HTMLFragment fragment, String id) {
        fragment2id.put(fragment, id);
    }
    
    public String getFragmentId(HTMLFragment fragment) {
        return (String)fragment2id.get(fragment);
    }
    
    public String toString () {
        return "HTMLFile with filename "+filename;
    }
    
    protected static String TOPANCHOR = "<!-- top anchor -->\n"
        + "<div id=\"top\"></div>\n\n";  
    protected static String TOPLINK = "<!-- top link -->\n"
        + "<hr /><div class=\"navtop\">"
        + "<a href=\"#top\">Top</a></div>\n\n";


    protected void writeTopAnchor ( StringBuffer out ) {
        out.append ( TOPANCHOR );
    }
    
    protected void writeTopLink ( StringBuffer out ) {
        out.append ( TOPLINK );
    }
    
    protected void writeNavBar ( StringBuffer out ) {
        out.append ( "<!-- navigation bar -->\n" );
        out.append ( "<div class=\"nav\">\n");
        
        //out.append ( "<span class=\"navitem\"><a href=\"index.html\">main page</a></span>\n" );
        
        boolean first = true;
        final Iterator it = htmlModel.files();
        while ( it.hasNext() ) {
            HTMLFile file = (HTMLFile)it.next();
            if ( !first ) {
                out.append( " | " );
            }
            out.append ( "<span class=\"navitem\">" );
            if ( file == this ) {
                out.append ( getShortTitle() );
            }
            else {
                out.append ( "<a href=\""+file.getFilename()+"\">"+file.getShortTitle()+"</a>" );
            }
            out.append ( "</span>" );
            first = false;
        }
        
        out.append ( "</div>\n\n" );
    }

    protected void writeHeader ( StringBuffer out ) {
        out.append(
            "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"+
            "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.1//EN\" \"http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd\">\n"+
            "<html xmlns=\"http://www.w3.org/1999/xhtml\" xml:lang=\"en\">\n"+
            "\n"+
            "<head>\n"+
            "<title>"+getTitle()+"</title>\n"+
            "<link rel=\"stylesheet\" href=\"style.css\" type=\"text/css\" />\n"+
            "</head>"+
            "\n"+
            "<body>\n"
            );
    }
    
    /** returns name displayed in title bar */
    protected abstract String getTitle ();
    
    /** returns name displayed in navigation bar */
    protected abstract String getShortTitle ();

    protected void writeFooter ( StringBuffer out ) {
        out.append ( "<div class=\"versioninfo\">" );
        out.append ( "<p>Generated from internal version " + PRCSVERSION + 
                " on " + formatDate () + ".</p>" );
        out.append ( "</div>" );
        out.append ( "</body>\n\n</html>\n" );
    }
    
    private String formatDate () {
        Date now = new Date();
        SimpleDateFormat formatter = new SimpleDateFormat ( "yyyy-MM-dd HH:mm z" );
        return formatter.format(now);
    }

    public void write () {
        try {
            OutputStreamWriter writer = null;
            if (false /* useGZIP */) {
                FileOutputStream fos = new FileOutputStream(htmlModel.getRootFolder() + getFilename() + ".gz");
                GZIPOutputStream gos = new GZIPOutputStream(fos);
                writer = new OutputStreamWriter(gos);
            } else {
                FileOutputStream fos = new FileOutputStream(htmlModel.getRootFolder() + getFilename());
                writer = new OutputStreamWriter(fos);
            }
            write(writer);
            writer.close();
        }
        catch (IOException e) {
            System.err.println(e);
        }
    }
    
    protected abstract void write ( Writer w ) throws IOException; 
    
    protected void init ( RuleExportModel model ) {
        this.model = model;
        //System.out.println("HTMLFile.init(), "+getFilename());
    }
    
    protected void writeTacletLink ( StringBuffer out, TacletModelInfo t ) {
        writeTacletLink ( out, t, false );
    }
    
    protected void writeTacletLink ( StringBuffer out, TacletModelInfo t,
            boolean longVersion ) {
        final HTMLLink link = getFragmentLink ( t );
        out.append ( link.toTag ( t.name() ) );
        if ( longVersion ) {
            if ( t.getIntroducingTaclet() != null ) {
                out.append ( " <" );
                writeTacletLink ( out, t.getIntroducingTaclet() );
                out.append ( ">" );
            }
            if ( t.getOptions().size() > 0 ) {
                out.append ( " (" );
                writeTacletOptions ( out, t );
                out.append ( ")" );
            }
        }
    }

    protected void writeRuleSetLink ( StringBuffer out, RuleSetModelInfo rs ) {
        final HTMLLink link = getFragmentLink ( rs );
        out.append ( link.toTag ( escape ( rs.name() ) ) );
    }
    
    protected void writeDisplayNameLink ( StringBuffer out, DisplayNameModelInfo dn ) {
        final HTMLLink link = getFragmentLink ( dn );
        out.append ( link.toTag ( dn ) );
    }
    
    protected void writeOptionLink ( StringBuffer out, OptionModelInfo opt ) {
        final HTMLLink link = getFragmentLink ( opt );
        out.append ( link.toTag( opt.name() ) );
    }

    protected void writeTacletOptions ( StringBuffer out, TacletModelInfo t ) {
        final ListOfOptionModelInfo options = t.getOptions ();
        
        writeOptionList ( out, options );
    }

    protected void writeOptionList ( StringBuffer out, ListOfOptionModelInfo options ) {
        final IteratorOfOptionModelInfo it = options.iterator();
        boolean first = true;
        while ( it.hasNext() ) {
            final OptionModelInfo opt = it.next ();
            if ( !first ) {
                out.append ( ", " );
            }
            writeOptionLink ( out, opt );
            first = false;
        }
    }

	protected StringBuffer appendEscaped(StringBuffer sb, Object o) {
	    return appendEscaped(sb, o.toString());
	}

	protected StringBuffer appendEscaped(StringBuffer sb, String s) {
	    for (int n = 0; n < s.length(); n++) {
	        switch (s.charAt(n)) {
	        case '"':
	            sb.append("&quot;");
	            break;
	        case '&':
	            sb.append("&amp;");
	            break;
	        case '<':
	            sb.append("&lt;");
	            break;
	        case '>':
	            sb.append("&gt;");
	            break;
	        //case '\n':
	        //    sb.append("<br />\n");
	        //    break;
	        default:
	            sb.append(s.charAt(n));
	        }
	    }
	    return sb;
	}
	
	protected String escape ( Object o ) {
		StringBuffer sb = new StringBuffer();
		appendEscaped(sb, o);
		return sb.toString();
	}
}
