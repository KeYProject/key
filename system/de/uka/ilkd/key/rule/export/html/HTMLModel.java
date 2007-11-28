// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export.html;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.net.URL;
import java.util.HashMap;

import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.KeYResourceManager;



public class HTMLModel extends HTMLContainer {
    private HashMap key2fragment = new HashMap();
    
    private HTMLFragment getFragment(Object key) {
        return (HTMLFragment)key2fragment.get(key);
    }
    
    private void putFragment(Object key, HTMLFragment fragment) {
        key2fragment.put(key, fragment);
    }
    
    public String getRelPath(HTMLFile source, HTMLFile target) {
        return target.getFilename();
    }
    
    public HTMLModel(String rootFolder) {
        super(rootFolder);
    }
    
    public void writeAllFiles () {
        super.writeAllFiles();
        
        writeStyleSheet ();
    }
    
    private void writeStyleSheet () {
        URL css = KeYResourceManager.getManager().getResourceFile(HTMLFile.class, "templates/style.css");
        copyFile ( css.getFile(), getRootFolder() + "style.css" );
    }
    
    private void copyFile (String from, String to) {
        FileReader reader;
        FileWriter writer;
        
        //System.out.println ( "copying file "+from+" to "+to);
        
        try {
            reader = new FileReader(from);
        }
        catch (FileNotFoundException e) {
            System.err.println ( e );
            return;
        }
        
        try {
            writer = new FileWriter(to);
        }
        catch (IOException e) {
            System.err.println ( e );
            return;
        }
        
        try {
            int ch;
            while ((ch = reader.read()) != -1) {
                writer.write(ch);
                //System.out.write(ch);
            }
            reader.close();
            writer.close();
        }
        catch (IOException e) {
            System.err.println ( e );
            return;
        }
    }
    
    public HTMLLink getFileLink ( HTMLFile source, HTMLFile target ) {
        return new HTMLFileLink ( source, target );
    }
    
    public HTMLLink getFragmentLink(HTMLFile sourceFile, Object targetKey) {
        HTMLFragment fragment = getFragment(targetKey);
        
        if (fragment == null) {
            fragment = new HTMLFragment(null, targetKey);
            putFragment(targetKey, fragment);
        }
        
        return new HTMLFragmentLink(sourceFile, fragment);        
    }
    
    public HTMLLink getTacletLink(final HTMLFile source, final Taclet t) {
        return getFragmentLink(source, t);
    }
    
    public HTMLAnchor getFragmentAnchor ( HTMLFile file, Object key ) {
        HTMLFragment fragment = getFragment ( key );
        
        if (fragment != null) {
            if ( fragment.getFile() == null ) {
                fragment.setFile(file);
                String id = file.getNextId();
                file.addFragment(fragment, id);
                //System.out.println("missing fragment definition: "+file.getFilename()+", "+key);
            } else {
                //System.out.println("ignored fragment redefinition: "+file.getFilename()+", "+key);
            }
        } else {
            fragment = new HTMLFragment(file, key);
            putFragment(key, fragment);
            String id = file.getNextId();
            file.addFragment(fragment, id);
            //System.out.println("fragment definition: "+file.getFilename()+", "+key);
        }
        
        final HTMLFragment f = fragment;

        return new HTMLAnchor () {
        
            public String toString () {
                return f.getId();
            }
        };
    }
}
