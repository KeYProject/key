<?php

# This file is the backend companion to the class SendFeedbackAction in
# the same directory which sends the current KeY proof state to our
# server in order to send to an email address, eventually to the key
# mailing list.
#
# This code stores the received ZIP file in a directory.
# This directory "key-feedback" has a .htaccess with "deny from all".
#
# Moreover it sends the zip file as an attachment to a set e-mail address
# For the moment that receiver is Mattias, but that can and will change
# over time.
#
# The productive version of this file is installed under
#   /misc/HomePages/i57/htdocs/key
#
# and can be modified by group "i12pro" which allows all KeY developers
# at KIT to hide or modify the script. Please backport changes to the
# repository copy in git
# (at key/key.ui/src/main/java/de/uka/ilkd/key/gui/actions).


# print_r($_SERVER);

###### UNCOMMENT THE FOLLOWING 3 LINES IF THE SCRIPT NEEDS
###### TO BE SHUTDOWN QUICKLY.
# http_response_code(400);
# echo "Service currently not available";
# exit;


if(!array_key_exists('HTTP_KEY_VERSION', $_SERVER)) {
    http_response_code(400);
    echo "Missing KeY version.";
    exit;
}

$keyVersion = $_SERVER['HTTP_KEY_VERSION'];

$version = substr($keyVersion, 0, 6);
if($version != "KeY 2.") {
    http_response_code(400);
    echo "Illegal KeY version $version.";
    exit;
}

$content = file_get_contents("php://input");
file_put_contents("key-feedback/key-" . time() . ".zip", $content);

$encoded = base64_encode($content);
$split = chunk_split($encoded);


// a random hash will be necessary to send mixed content
$separator = md5(time());

$to = "ulbrich@kit.edu";
$subject = "KeY feedback from within the tool" ;
$message = "This feedback report has been triggered from within the KeY tool.\n" .
	"Please find further information about the bug in the attached zip file.\n\n" .
        "The person who gave the feedback may wait for answer if they added\n".
	"their mail address.";

// carriage return type (RFC)
$eol = "\r\n";

// main header (multipart mandatory)
$headers = 'From: KeY application feedback <ulbrich@kit.edu>' . $eol;
$headers .= "MIME-Version: 1.0" . $eol;
$headers .= "Content-Type: multipart/mixed; boundary=\"" . $separator . "\"" . $eol;
$headers .= "Content-Transfer-Encoding: 7bit" . $eol;
$headers .= "This is a MIME encoded message." . $eol;

// message
$body = "--" . $separator . $eol;
$body .= "Content-Type: text/plain; charset=\"iso-8859-1\"" . $eol;
$body .= "Content-Transfer-Encoding: 8bit" . $eol;
$body .= $eol . $message . $eol . $eol;

// attachment
$body .= "--" . $separator . $eol;
$body .= "Content-Type: application/octet-stream; name=\"KeY-bug-description.zip\"" . $eol;
$body .= "Content-Disposition: attachment; filename=KeY-bug-description.zip" . $eol;
$body .= "Content-Transfer-Encoding: base64" . $eol . $eol;
$body .= $split . $eol;
$body .= "--" . $separator . "--";

if (mail($to, $subject, $body, $headers)) {
    echo "mail send ... OK"; // or use booleans here
} else {
    http_response_code(500);
    header("HTTP/1.0 500 Cannot send e-mail");
    echo "mail send ... ERROR!";
    print_r( error_get_last() );
    print_r($body);
    exit;
}

echo "OK. Your message has been sent.";



?>
