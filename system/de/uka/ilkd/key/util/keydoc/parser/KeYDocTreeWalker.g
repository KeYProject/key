// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
header { package de.uka.ilkd.key.util.keydoc.parser; import java.util.LinkedList; }


class KeYDocTreeWalker extends TreeParser;

options { importVocab= KeYDocParser; exportVocab= KeYDocTreeWalker; }
{ public StringBuffer version= null;   
    public StringBuffer since= null;
    public StringBuffer provable= null;
    public boolean deprecated= false;
    
    public LinkedList see= new LinkedList();
    public LinkedList stat1= new LinkedList();
    public LinkedList stat2= new LinkedList();
    public LinkedList auth= new LinkedList();
    public LinkedList elem= new LinkedList();
    public LinkedList link= new LinkedList();
    public LinkedList startlink= new LinkedList();

  
}

keyDocExpr :
        (#(OPENDOC (tag)*))? ; 

tag {StringBuffer temp=new StringBuffer(), temp2=new StringBuffer(); boolean bool=false;}:

    #(PROVABLE provable=ebase) |

    ((#(SEE IDENT)) =>
        #(SEE i:IDENT
                {temp.append("<a href=").append(i.getText());}
        (temp2=base {temp.append(temp2);})*
                {temp.append(".html>");}
        (WS (temp2=ebase
                {temp.append(temp2);}
            )+ {bool=true;})?  
                {if (!bool) temp.append(i.getText()); bool=false; temp.append("</a>"); see.add(temp);}
        ) |
        #(SEE  ((temp2=ebase | HTTPSTART {temp2.append("<a href=");}) {temp.append(temp2); })+ {see.add(temp);})
    ) |

    ((#(LINK IDENT)) =>
        #(LINK l:IDENT
                {temp.append("<a href=").append(l.getText());}
        (temp2=base {temp.append(temp2);})*
                {temp.append(".html>");}
        (WS (temp2=ebase
                {temp.append(temp2);}
            )+  {bool=true;})?
                {if (!bool) temp.append(l.getText()); bool=false; temp.append("</a>"); link.add(temp);}
        ) |
        #(LINK  ((temp2=ebase | HTTPSTART {temp2.append("<a href=");}) {temp.append(temp2); })+ {link.add(temp);})
    ) |

    #(VERSION (temp2=ebase {temp.append(temp2);})+ {version=temp;}) |
    #(SINCE (temp2=ebase {temp.append(temp2); })+ {since=temp;}) |
    #(AUTHOR (temp2=ebase {temp.append(temp2);})+ {auth.add(temp);}) |
    #(DEPRECATED {deprecated=true;}) |
    #(STATISTIC i3:IDENT (i4:IDENT {temp2.append(i4.getText());} |
                          in:INT {temp2.append(in.getText());})
                          {temp=temp.append(i3.getText()); stat1.add(temp); stat2.add(temp2); })
        ;
        
        

base returns [StringBuffer baseValue] {baseValue= new StringBuffer();}:
         a:IDENT {baseValue.append(a.getText());}|
         b:OTHERTEXT {baseValue.append(b.getText());} | 
         c:INT {baseValue.append(c.getText());} |
         d:DOT {baseValue.append(d.getText());} |
         //e:WS {baseValue.append(e.getText());} | 
         f:HASH {baseValue.append(f.getText());} | 
         g:SLASH {baseValue.append(g.getText());} |
         h:STAR {baseValue.append(h.getText());} | 
         i:AT {baseValue.append(i.getText());} | 
         j:OPENDOC {baseValue.append(j.getText());} | 
         k:PROVABLE {baseValue.append(k.getText());} |
         l:SEE {baseValue.append(l.getText());} | 
         m:VERSION {baseValue.append(m.getText());} |
         n:SINCE {baseValue.append(n.getText());} |
         o:AUTHOR {baseValue.append(o.getText());} |
         p:DEPRECATED {baseValue.append(p.getText());} | 
         q:STATISTIC {baseValue.append(q.getText());}|
         s:LINK {baseValue.append(s.getText());} |
         t:HTTPEND {baseValue.append(t.getText());} |
         u:MT {baseValue.append(u.getText());} |
         v:RIGHTBRACKET {baseValue.append(v.getText());} |
         w:QUOTE {baseValue.append(w.getText());} |
       //  x:HTTPSTART {baseValue.append(x.getText());} |  
         (y:LEFTBRACKET {baseValue.append(y.getText());})
         ;

// TODO: HTTPSTART PROBLEM!!
ebase returns [StringBuffer baseValue] {baseValue= new StringBuffer();}:
         a:IDENT {baseValue.append(a.getText());}|
         b:OTHERTEXT {baseValue.append(b.getText());} | 
         c:INT {baseValue.append(c.getText());} |
         d:DOT {baseValue.append(d.getText());} |
         e:WS {baseValue.append(e.getText());} | 
         f:HASH {baseValue.append(f.getText());} | 
         g:SLASH {baseValue.append(g.getText());} |
         h:STAR {baseValue.append(h.getText());} | 
         i:AT {baseValue.append(i.getText());} | 
         j:OPENDOC {baseValue.append(j.getText());} | 
         k:PROVABLE {baseValue.append(k.getText());} |
         l:SEE {baseValue.append(l.getText());} | 
         m:VERSION {baseValue.append(m.getText());} |
         n:SINCE {baseValue.append(n.getText());} |
         o:AUTHOR {baseValue.append(o.getText());} |
         p:DEPRECATED {baseValue.append(p.getText());} | 
         q:STATISTIC {baseValue.append(q.getText());}|
         s:LINK {baseValue.append(s.getText());} |
         t:HTTPEND {baseValue.append(t.getText());} |
         u:MT {baseValue.append(u.getText());} |
         v:RIGHTBRACKET {baseValue.append(v.getText());} |
         w:QUOTE {baseValue.append(w.getText());} |
         y:LEFTBRACKET {baseValue.append(y.getText());}
         ;
