// This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export.html;

public class HTMLFragment {

    private HTMLFile file;

    private Object   key;

    public HTMLFragment ( HTMLFile file, Object key ) {
        this.file = file;
        this.key = key;
    }

    /**
     * @return Returns the file.
     */
    public HTMLFile getFile () {
        return file;
    }

    /**
     * @param file
     *            The file to set.
     */
    public void setFile ( HTMLFile file ) {
        this.file = file;
    }

    /**
     * @return Returns the key.
     */
    public Object getKey () {
        return key;
    }
    
    public String getId () {
        if (key == null) {
            return null;
        }
        if ( file == null ) {
            return "";
        }
        return file.getFragmentId(this);
    }
}
