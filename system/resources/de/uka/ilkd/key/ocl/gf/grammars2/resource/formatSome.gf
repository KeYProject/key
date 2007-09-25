-- This file contains opers for constructing text without any special
-- formatting. A few small formatting steps are used. 
-- E.g. "(*)" is used for bullets.

instance formatSome of format = {


oper     
      

--    
-- Formatting type details
--

    mkFormatHeader : Str -> Str -> Str -> Str = \a,b,c -> "";
    mkFormatFooter = "";
    mkTitle : Str -> Str = \str -> "";
    mkHeading : Str -> Str = \str -> "";
    mkStyle : Str -> Str = \str -> "";
    
    
--    
-- Formatting words, paragraphs
--
      
    mkLineBreak = ""; 
    mkDivide = ""; 
    mkBold : Str -> Str = \text -> text;
    mkItalic : Str -> Str = \text -> text;
    mkCode : Str -> Str = \text -> text;
    mkNote : Str -> Str -> Str = \text, tooltip -> text;
    
    mkStartBlock = "";
    mkEndBlock = "";    
    mkBlock : Str -> Str = \text -> text;
    

--    
-- Formatting lists
--  

    mkStartList = "";
    mkEndList = "";
    mkBullet = "(*)";
    
    -- Wrap a 'bulleted' string in the appropriate tags.
    wrapBullets : Str -> Str = \str -> mkStartList ++ str ++ mkEndList;        
    
    -- Place a bullet between two strings        
    bulletInfix : Str -> Str -> Str = \a,b -> a ++ mkBullet ++ b;    
    
    -- Place a bullet before a string
    bulletPrefix : Str -> Str = \a -> mkBullet ++ a;
};
