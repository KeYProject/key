// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

/** StringBuffer with more functionality.
 * To be completed to have a compatible API with StringBuffer.
 * @author bruns
 */
public class EnhancedStringBuffer
{

    private StringBuffer sb;
    
    public EnhancedStringBuffer() {
        sb = new StringBuffer();
    }
    
    public EnhancedStringBuffer(int capacity){
        sb = new StringBuffer(capacity);
    }
    
    public EnhancedStringBuffer(StringBuffer buffer) {
        sb = buffer;
    }
    
    public EnhancedStringBuffer(CharSequence proto){
        sb = new StringBuffer(proto);
    }
    
    public EnhancedStringBuffer(char singleton){
        sb = new StringBuffer();
        sb.append(singleton);
    }
    
    public EnhancedStringBuffer append (CharSequence s) {
        sb.append(s);
        return this;
    }
    
    public EnhancedStringBuffer append (char c) {
        sb.append(c);
        return this;
    }
    
    public EnhancedStringBuffer append (long l) {
        sb.append(l);
        return this;
    }
    
    public char charAt (int pos) {
        return sb.charAt(pos);
    }
    
    public int length () {
        return sb.length();
    }
    
    public EnhancedStringBuffer prepend (CharSequence s) {
        StringBuffer tmp = sb;
        sb = new StringBuffer(s);
        sb.append(tmp);
        return this;
    }
    
    public EnhancedStringBuffer prepend (char c) {
        StringBuffer tmp = sb;
        sb = new StringBuffer();
        sb.append(c);
        sb.append(tmp);
        return this;
    }

    public EnhancedStringBuffer deleteCharAt(int i) {
        sb.deleteCharAt(i);
        return this;
    }
    


    /** Return time information (in milliseconds)
     * in human-readable format.
     */
    public static EnhancedStringBuffer formatTime (long ms) {
        EnhancedStringBuffer res = new EnhancedStringBuffer();
        if (ms < 10000) {
            res.append(ms);
            res.append("ms");
        }
        else {
            final long sec = ms/1000;
            if (sec < 360) {
                res.append(sec);
                res.append('.');
                res.append((ms/100)%10);
                res.append('s');
            }
            else {
                long min = sec/60;
                if (min < 120) {
                    res.append(min);
                    res.append("min");
                } else {
                    final long h = min/60;
                    min %= 60;   
                    res.append(h);
                    res.append("h ");
                    res.append(min);
                    res.append("min");
                }
            }
        }
        return res;
    }
    
    /** Format an integer human-readable (i.e., using decimal separators)
     */
    public static EnhancedStringBuffer format (long number) {
        String tmp = ""+number;
        EnhancedStringBuffer res = new EnhancedStringBuffer();
        for (int i= tmp.length()-1; i >= 0; i--) {
            res.prepend(tmp.charAt(i));
            if ((tmp.length()-1-i)%3==2) res.prepend(',');
        }
        if (res.length() > 0 && res.charAt(0)==',') res.deleteCharAt(0);
        return res;
    }
    
    @Override
    public String toString() {
        return sb.toString();
    }
}