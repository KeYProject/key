-- This file contains opers for formatting text using HTML
-- To get the full power of the HTML formatting, a style sheet should be used.
-- E.g. (from coreEng.gf)
-- document cs = {s = (mkFormatHeader (mkTitle ("OCL" ++ "Constraints"))
--      (mkHeading ("OCL" ++ "Constraints")) (mkStyle "OCLstyle.css"))
--      ++ cs.s ++ mkFormatFooter};
--


instance formatHTML of format = open HTML in {

--# -path=.:prelude

oper
    
    -- This oper could be added to the HTML resource module.
    tagAttr : Str -> Str -> Str = 
      \t,a -> ("<" + t) ++ (a + ">");    



--    
-- Formatting type details
--
    
    mkTitle : Str -> Str = \title -> intag "title" title;    
    mkHeading : Str -> Str = \heading -> intag "h1" heading;
    mkStyle : Str -> Str = \style ->
        tagAttr "link" ("rel=\"stylesheet\"" ++ "type=\"text/css\"" ++ "href=\"" + style + "\"");
            
    -- Format Header can be given a title, heading and sytlesheet if desisred.
    -- If none are needed, simply pass empty strings.
    mkFormatHeader : Str -> Str -> Str -> Str = \title, heading, style -> 
        (tag "html") + (tag "head") + title + style + (endtag "head") +
        (tag "body") + heading;
    mkFormatFooter = endtag "body" + endtag "html";    
    
    
--    
-- Formatting words, paragraphs
--

    mkLineBreak = tag "br"; 
    mkDivide = tag "p" + tag "hr" + tag "p"; 
    mkBold : Str -> Str = \text -> intag "b" text;
    mkItalic : Str -> Str = \text -> intag "i" text;
    mkCode : Str -> Str = \text -> intagAttr "span" "class=code" text;
    
    mkStartBlock = tagAttr "div" "class=block";
    mkEndBlock = endtag "div";    
    mkBlock : Str -> Str = \text -> mkStartBlock ++ text ++ mkEndBlock;
    mkNote : Str -> Str -> Str = \text, tooltip ->
        intagAttr "acronym" ("title="+"\""+tooltip+"\"") (mkCode text);


--    
-- Formatting lists
--  
    
    mkStartList = tag "ul";
    mkEndList = endtag "ul";
    mkBullet = tag "li";
    
    -- Wrap a 'bulleted' string in the appropriate tags.
    wrapBullets : Str -> Str = \str -> mkStartList ++ str ++ mkEndList;        
    
    -- Place a bullet between two strings        
    bulletInfix : Str -> Str -> Str = \a,b -> a ++ mkBullet ++ b;    
    
    -- Place a bullet before a string
    bulletPrefix : Str -> Str = \a -> mkBullet ++ a;
        
};
