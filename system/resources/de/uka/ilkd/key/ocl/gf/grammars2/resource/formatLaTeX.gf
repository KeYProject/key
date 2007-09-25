-- This file contains opers for formatting text using LaTeX

instance formatLaTeX of format = open Prelude,Latex in {

--# -path=.:prelude

oper
    
    command1 : Str -> Str -> Str = \f,x -> (command f) + "{" + x + "}" ;
    
    command2 : Str -> Str -> Str -> Str = 
      \f,x,y -> (command f) + "{" ++ x ++ "}{" ++ y ++ "}" ;
            



--    
-- Formatting type details
--

    
    -- Format Header can be given a title, heading and style if desisred.
    -- Currently, for latex, the heading and style are ignored.
    mkFormatHeader : Str -> Str -> Str -> Str = \title, heading, style -> 
        (command1 "documentclass" "article") ++ (command1 "title" title) 
        ++ (begin "document") ++ (command "maketitle") ++ (command "flushleft") 
        ++ (command2 "setlength" "\\parskip" "1em");
--        ++ (command "maketitle");

    mkFormatFooter = end "document";    
    
    mkTitle : Str -> Str = \str -> str;
    mkHeading : Str -> Str = \str -> str;
    mkStyle : Str -> Str = \str -> str;
    
    
--    
-- Formatting words, paragraphs
--
      
    mkLineBreak = command "newline"; 
    mkDivide = (command "par") ++ (command2 "rule" "10cm" ".1pt") 
        ++ (command "par"); 
    
    -- For some reason... if I use command1 with these three, then they dont work!
    mkBold : Str -> Str = \text -> "\\textbf{"  ++ text ++ "}"; -- use "glue" here    
    mkItalic : Str -> Str = \text -> "\\textit{" ++ text ++ "}"; -- use "glue" here 
    mkCode : Str -> Str = \text -> "\\texttt{" ++ text ++ "}"; -- use "glue" here 
    
    mkNote : Str -> Str -> Str = \text, tooltip -> (mkCode text) ++ (command1 "footnote" tooltip);
    
    -- \newenvironment{block}{\newline \setlength{\parindent}{1cm} \indent}{}
    mkStartBlock = mkLineBreak ++ (command "indent");
    mkEndBlock = "";    
    mkBlock : Str -> Str = \text -> mkStartBlock ++ text ++ mkEndBlock;
    

--    
-- Formatting lists
--  

    mkStartList = begin "itemize";
    mkEndList = end "itemize";
    mkBullet = command "item";
    
    -- Wrap a 'bulleted' string in the appropriate tags.
    wrapBullets : Str -> Str = \str -> mkStartList ++ str ++ mkEndList;        
    
    -- Place a bullet between two strings        
    bulletInfix : Str -> Str -> Str = \a,b -> a ++ mkBullet ++ b;    
    
    -- Place a bullet before a string
    bulletPrefix : Str -> Str = \a -> mkBullet ++ a;
  
                    
    
};
