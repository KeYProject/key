-- This file contains opers for formatting text.

interface format = {


oper
            
    

--    
-- Formatting type details
--

    mkFormatHeader : Str -> Str -> Str -> Str;
    mkFormatFooter : Str;
    mkTitle : Str -> Str;
    mkHeading : Str -> Str;
    mkStyle : Str -> Str;

    
--    
-- Formatting words, paragraphs
--
    
    mkLineBreak : Str;
    mkDivide : Str;
    mkBold : Str -> Str;
    mkItalic : Str -> Str;
    mkCode : Str -> Str;
    mkStartBlock : Str;
    mkEndBlock : Str;
    mkBlock : Str -> Str;
    mkNote : Str -> Str -> Str;


--    
-- Formatting lists
--    

    mkStartList : Str;
    mkEndList : Str;
    mkBullet : Str; 
    
    -- Wrap a 'bulleted' string in the appropriate tags.
    wrapBullets : Str -> Str;
    
    -- Place a bullet between two strings        
    bulletInfix : Str -> Str -> Str;
    
    -- Place a bullet before a string
    bulletPrefix : Str -> Str;


};
