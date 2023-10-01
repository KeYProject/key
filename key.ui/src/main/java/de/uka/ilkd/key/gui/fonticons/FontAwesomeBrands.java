/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.fonticons;

import java.awt.*;
import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (22.07.19)
 */
public enum FontAwesomeBrands implements IconFont {
    _500PX('\uf26e'), ACCESSIBLE_ICON('\uf368'), ACCUSOFT('\uf369'),
    ACQUISITIONS_INCORPORATED('\uf6af'), ADN('\uf170'), ADOBE('\uf778'), ADVERSAL('\uf36a'),
    AFFILIATETHEME('\uf36b'), AIRBNB('\uf834'), ALGOLIA('\uf36c'), ALIPAY('\uf642'),
    AMAZON('\uf270'), AMAZON_PAY('\uf42c'), AMILIA('\uf36d'), ANDROID('\uf17b'),
    ANGELLIST('\uf209'), ANGRYCREATIVE('\uf36e'), ANGULAR('\uf420'), APP_STORE('\uf36f'),
    APP_STORE_IOS('\uf370'), APPER('\uf371'), APPLE('\uf179'), APPLE_PAY('\uf415'),
    ARTSTATION('\uf77a'), ASYMMETRIK('\uf372'), ATLASSIAN('\uf77b'), AUDIBLE('\uf373'),
    AUTOPREFIXER('\uf41c'), AVIANEX('\uf374'), AVIATO('\uf421'), AWS('\uf375'), BANDCAMP('\uf2d5'),
    BATTLE_NET('\uf835'), BEHANCE('\uf1b4'), BEHANCE_SQUARE('\uf1b5'), BIMOBJECT('\uf378'),
    BITBUCKET('\uf171'), BITCOIN('\uf379'), BITY('\uf37a'), BLACK_TIE('\uf27e'),
    BLACKBERRY('\uf37b'), BLOGGER('\uf37c'), BLOGGER_B('\uf37d'), BLUETOOTH('\uf293'),
    BLUETOOTH_B('\uf294'), BOOTSTRAP('\uf836'), BTC('\uf15a'), BUFFER('\uf837'),
    BUROMOBELEXPERTE('\uf37f'), BUYSELLADS('\uf20d'), CANADIAN_MAPLE_LEAF('\uf785'),
    CC_AMAZON_PAY('\uf42d'), CC_AMEX('\uf1f3'), CC_APPLE_PAY('\uf416'), CC_DINERS_CLUB('\uf24c'),
    CC_DISCOVER('\uf1f2'), CC_JCB('\uf24b'), CC_MASTERCARD('\uf1f1'), CC_PAYPAL('\uf1f4'),
    CC_STRIPE('\uf1f5'), CC_VISA('\uf1f0'), CENTERCODE('\uf380'), CENTOS('\uf789'),
    CHROME('\uf268'), CHROMECAST('\uf838'), CLOUDSCALE('\uf383'), CLOUDSMITH('\uf384'),
    CLOUDVERSIFY('\uf385'), CODEPEN('\uf1cb'), CODIEPIE('\uf284'), CONFLUENCE('\uf78d'),
    CONNECTDEVELOP('\uf20e'), CONTAO('\uf26d'), CPANEL('\uf388'), CREATIVE_COMMONS('\uf25e'),
    CREATIVE_COMMONS_BY('\uf4e7'), CREATIVE_COMMONS_NC('\uf4e8'), CREATIVE_COMMONS_NC_EU('\uf4e9'),
    CREATIVE_COMMONS_NC_JP('\uf4ea'), CREATIVE_COMMONS_ND('\uf4eb'), CREATIVE_COMMONS_PD('\uf4ec'),
    CREATIVE_COMMONS_PD_ALT('\uf4ed'), CREATIVE_COMMONS_REMIX('\uf4ee'),
    CREATIVE_COMMONS_SA('\uf4ef'), CREATIVE_COMMONS_SAMPLING('\uf4f0'),
    CREATIVE_COMMONS_SAMPLING_PLUS('\uf4f1'), CREATIVE_COMMONS_SHARE('\uf4f2'),
    CREATIVE_COMMONS_ZERO('\uf4f3'), CRITICAL_ROLE('\uf6c9'), CSS3('\uf13c'), CSS3_ALT('\uf38b'),
    CUTTLEFISH('\uf38c'), D_AND_D('\uf38d'), D_AND_D_BEYOND('\uf6ca'), DASHCUBE('\uf210'),
    DELICIOUS('\uf1a5'), DEPLOYDOG('\uf38e'), DESKPRO('\uf38f'), DEV('\uf6cc'),
    DEVIANTART('\uf1bd'), DHL('\uf790'), DIASPORA('\uf791'), DIGG('\uf1a6'),
    DIGITAL_OCEAN('\uf391'), DISCORD('\uf392'), DISCOURSE('\uf393'), DOCHUB('\uf394'),
    DOCKER('\uf395'), DRAFT2DIGITAL('\uf396'), DRIBBBLE('\uf17d'), DRIBBBLE_SQUARE('\uf397'),
    DROPBOX('\uf16b'), DRUPAL('\uf1a9'), DYALOG('\uf399'), EARLYBIRDS('\uf39a'), EBAY('\uf4f4'),
    EDGE('\uf282'), ELEMENTOR('\uf430'), ELLO('\uf5f1'), EMBER('\uf423'), EMPIRE('\uf1d1'),
    ENVIRA('\uf299'), ERLANG('\uf39d'), ETHEREUM('\uf42e'), ETSY('\uf2d7'), EVERNOTE('\uf839'),
    EXPEDITEDSSL('\uf23e'), FACEBOOK('\uf09a'), FACEBOOK_F('\uf39e'), FACEBOOK_MESSENGER('\uf39f'),
    FACEBOOK_SQUARE('\uf082'), FANTASY_FLIGHT_GAMES('\uf6dc'), FEDEX('\uf797'), FEDORA('\uf798'),
    FIGMA('\uf799'), FIREFOX('\uf269'), FIRST_ORDER('\uf2b0'), FIRST_ORDER_ALT('\uf50a'),
    FIRSTDRAFT('\uf3a1'), FLICKR('\uf16e'), FLIPBOARD('\uf44d'), FLY('\uf417'),
    FONT_AWESOME('\uf2b4'), FONT_AWESOME_ALT('\uf35c'), FONT_AWESOME_FLAG('\uf425'),
    FONT_AWESOME_LOGO_FULL('\uf4e6'), FONTICONS('\uf280'), FONTICONS_FI('\uf3a2'),
    FORT_AWESOME('\uf286'), FORT_AWESOME_ALT('\uf3a3'), FORUMBEE('\uf211'), FOURSQUARE('\uf180'),
    FREE_CODE_CAMP('\uf2c5'), FREEBSD('\uf3a4'), FULCRUM('\uf50b'), GALACTIC_REPUBLIC('\uf50c'),
    GALACTIC_SENATE('\uf50d'), GET_POCKET('\uf265'), GG('\uf260'), GG_CIRCLE('\uf261'),
    GIT('\uf1d3'), GIT_ALT('\uf841'), GIT_SQUARE('\uf1d2'), GITHUB('\uf09b'), GITHUB_ALT('\uf113'),
    GITHUB_SQUARE('\uf092'), GITKRAKEN('\uf3a6'), GITLAB('\uf296'), GITTER('\uf426'),
    GLIDE('\uf2a5'), GLIDE_G('\uf2a6'), GOFORE('\uf3a7'), GOODREADS('\uf3a8'),
    GOODREADS_G('\uf3a9'), GOOGLE('\uf1a0'), GOOGLE_DRIVE('\uf3aa'), GOOGLE_PLAY('\uf3ab'),
    GOOGLE_PLUS('\uf2b3'), GOOGLE_PLUS_G('\uf0d5'), GOOGLE_PLUS_SQUARE('\uf0d4'),
    GOOGLE_WALLET('\uf1ee'), GRATIPAY('\uf184'), GRAV('\uf2d6'), GRIPFIRE('\uf3ac'),
    GRUNT('\uf3ad'), GULP('\uf3ae'), HACKER_NEWS('\uf1d4'), HACKER_NEWS_SQUARE('\uf3af'),
    HACKERRANK('\uf5f7'), HIPS('\uf452'), HIRE_A_HELPER('\uf3b0'), HOOLI('\uf427'),
    HORNBILL('\uf592'), HOTJAR('\uf3b1'), HOUZZ('\uf27c'), HTML5('\uf13b'), HUBSPOT('\uf3b2'),
    IMDB('\uf2d8'), INSTAGRAM('\uf16d'), INTERCOM('\uf7af'), INTERNET_EXPLORER('\uf26b'),
    INVISION('\uf7b0'), IOXHOST('\uf208'), ITCH_IO('\uf83a'), ITUNES('\uf3b4'),
    ITUNES_NOTE('\uf3b5'), JAVA('\uf4e4'), JEDI_ORDER('\uf50e'), JENKINS('\uf3b6'), JIRA('\uf7b1'),
    JOGET('\uf3b7'), JOOMLA('\uf1aa'), JS('\uf3b8'), JS_SQUARE('\uf3b9'), JSFIDDLE('\uf1cc'),
    KAGGLE('\uf5fa'), KEYBASE('\uf4f5'), KEYCDN('\uf3ba'), KICKSTARTER('\uf3bb'),
    KICKSTARTER_K('\uf3bc'), KORVUE('\uf42f'), LARAVEL('\uf3bd'), LASTFM('\uf202'),
    LASTFM_SQUARE('\uf203'), LEANPUB('\uf212'), LESS('\uf41d'), LINE('\uf3c0'), LINKEDIN('\uf08c'),
    LINKEDIN_IN('\uf0e1'), LINODE('\uf2b8'), LINUX('\uf17c'), LYFT('\uf3c3'), MAGENTO('\uf3c4'),
    MAILCHIMP('\uf59e'), MANDALORIAN('\uf50f'), MARKDOWN('\uf60f'), MASTODON('\uf4f6'),
    MAXCDN('\uf136'), MEDAPPS('\uf3c6'), MEDIUM('\uf23a'), MEDIUM_M('\uf3c7'), MEDRT('\uf3c8'),
    MEETUP('\uf2e0'), MEGAPORT('\uf5a3'), MENDELEY('\uf7b3'), MICROSOFT('\uf3ca'), MIX('\uf3cb'),
    MIXCLOUD('\uf289'), MIZUNI('\uf3cc'), MODX('\uf285'), MONERO('\uf3d0'), NAPSTER('\uf3d2'),
    NEOS('\uf612'), NIMBLR('\uf5a8'), NODE('\uf419'), NODE_JS('\uf3d3'), NPM('\uf3d4'),
    NS8('\uf3d5'), NUTRITIONIX('\uf3d6'), ODNOKLASSNIKI('\uf263'), ODNOKLASSNIKI_SQUARE('\uf264'),
    OLD_REPUBLIC('\uf510'), OPENCART('\uf23d'), OPENID('\uf19b'), OPERA('\uf26a'),
    OPTIN_MONSTER('\uf23c'), OSI('\uf41a'), PAGE4('\uf3d7'), PAGELINES('\uf18c'), PALFED('\uf3d8'),
    PATREON('\uf3d9'), PAYPAL('\uf1ed'), PENNY_ARCADE('\uf704'), PERISCOPE('\uf3da'),
    PHABRICATOR('\uf3db'), PHOENIX_FRAMEWORK('\uf3dc'), PHOENIX_SQUADRON('\uf511'), PHP('\uf457'),
    PIED_PIPER('\uf2ae'), PIED_PIPER_ALT('\uf1a8'), PIED_PIPER_HAT('\uf4e5'),
    PIED_PIPER_PP('\uf1a7'), PINTEREST('\uf0d2'), PINTEREST_P('\uf231'), PINTEREST_SQUARE('\uf0d3'),
    PLAYSTATION('\uf3df'), PRODUCT_HUNT('\uf288'), PUSHED('\uf3e1'), PYTHON('\uf3e2'), QQ('\uf1d6'),
    QUINSCAPE('\uf459'), QUORA('\uf2c4'), R_PROJECT('\uf4f7'), RASPBERRY_PI('\uf7bb'),
    RAVELRY('\uf2d9'), REACT('\uf41b'), REACTEUROPE('\uf75d'), README('\uf4d5'), REBEL('\uf1d0'),
    RED_RIVER('\uf3e3'), REDDIT('\uf1a1'), REDDIT_ALIEN('\uf281'), REDDIT_SQUARE('\uf1a2'),
    REDHAT('\uf7bc'), RENREN('\uf18b'), REPLYD('\uf3e6'), RESEARCHGATE('\uf4f8'),
    RESOLVING('\uf3e7'), REV('\uf5b2'), ROCKETCHAT('\uf3e8'), ROCKRMS('\uf3e9'), SAFARI('\uf267'),
    SALESFORCE('\uf83b'), SASS('\uf41e'), SCHLIX('\uf3ea'), SCRIBD('\uf28a'), SEARCHENGIN('\uf3eb'),
    SELLCAST('\uf2da'), SELLSY('\uf213'), SERVICESTACK('\uf3ec'), SHIRTSINBULK('\uf214'),
    SHOPWARE('\uf5b5'), SIMPLYBUILT('\uf215'), SISTRIX('\uf3ee'), SITH('\uf512'), SKETCH('\uf7c6'),
    SKYATLAS('\uf216'), SKYPE('\uf17e'), SLACK('\uf198'), SLACK_HASH('\uf3ef'),
    SLIDESHARE('\uf1e7'), SNAPCHAT('\uf2ab'), SNAPCHAT_GHOST('\uf2ac'), SNAPCHAT_SQUARE('\uf2ad'),
    SOUNDCLOUD('\uf1be'), SOURCETREE('\uf7d3'), SPEAKAP('\uf3f3'), SPEAKER_DECK('\uf83c'),
    SPOTIFY('\uf1bc'), SQUARESPACE('\uf5be'), STACK_EXCHANGE('\uf18d'), STACK_OVERFLOW('\uf16c'),
    STACKPATH('\uf842'), STAYLINKED('\uf3f5'), STEAM('\uf1b6'), STEAM_SQUARE('\uf1b7'),
    STEAM_SYMBOL('\uf3f6'), STICKER_MULE('\uf3f7'), STRAVA('\uf428'), STRIPE('\uf429'),
    STRIPE_S('\uf42a'), STUDIOVINARI('\uf3f8'), STUMBLEUPON('\uf1a4'), STUMBLEUPON_CIRCLE('\uf1a3'),
    SUPERPOWERS('\uf2dd'), SUPPLE('\uf3f9'), SUSE('\uf7d6'), SYMFONY('\uf83d'), TEAMSPEAK('\uf4f9'),
    TELEGRAM('\uf2c6'), TELEGRAM_PLANE('\uf3fe'), TENCENT_WEIBO('\uf1d5'), THE_RED_YETI('\uf69d'),
    THEMECO('\uf5c6'), THEMEISLE('\uf2b2'), THINK_PEAKS('\uf731'), TRADE_FEDERATION('\uf513'),
    TRELLO('\uf181'), TRIPADVISOR('\uf262'), TUMBLR('\uf173'), TUMBLR_SQUARE('\uf174'),
    TWITCH('\uf1e8'), TWITTER('\uf099'), TWITTER_SQUARE('\uf081'), TYPO3('\uf42b'), UBER('\uf402'),
    UBUNTU('\uf7df'), UIKIT('\uf403'), UNIREGISTRY('\uf404'), UNTAPPD('\uf405'), UPS('\uf7e0'),
    USB('\uf287'), USPS('\uf7e1'), USSUNNAH('\uf407'), VAADIN('\uf408'), VIACOIN('\uf237'),
    VIADEO('\uf2a9'), VIADEO_SQUARE('\uf2aa'), VIBER('\uf409'), VIMEO('\uf40a'),
    VIMEO_SQUARE('\uf194'), VIMEO_V('\uf27d'), VINE('\uf1ca'), VK('\uf189'), VNV('\uf40b'),
    VUEJS('\uf41f'), WAZE('\uf83f'), WEEBLY('\uf5cc'), WEIBO('\uf18a'), WEIXIN('\uf1d7'),
    WHATSAPP('\uf232'), WHATSAPP_SQUARE('\uf40c'), WHMCS('\uf40d'), WIKIPEDIA_W('\uf266'),
    WINDOWS('\uf17a'), WIX('\uf5cf'), WIZARDS_OF_THE_COAST('\uf730'), WOLF_PACK_BATTALION('\uf514'),
    WORDPRESS('\uf19a'), WORDPRESS_SIMPLE('\uf411'), WPBEGINNER('\uf297'), WPEXPLORER('\uf2de'),
    WPFORMS('\uf298'), WPRESSR('\uf3e4'), XBOX('\uf412'), XING('\uf168'), XING_SQUARE('\uf169'),
    Y_COMBINATOR('\uf23b'), YAHOO('\uf19e'), YAMMER('\uf840'), YANDEX('\uf413'),
    YANDEX_INTERNATIONAL('\uf414'), YARN('\uf7e3'), YELP('\uf1e9'), YOAST('\uf2b1'),
    YOUTUBE('\uf167'), YOUTUBE_SQUARE('\uf431'), ZHIHU('\uf63f');

    private static Font font;
    private final char unicode;

    FontAwesomeBrands(char c) {
        unicode = c;
    }

    @Override
    public Font getFont() throws IOException, FontFormatException {
        if (font == null) {
            font = Font.createFont(Font.TRUETYPE_FONT,
                getClass().getResourceAsStream("/fonts/Font Awesome 6 Brands-Regular-400.otf"));
        }
        return font;
    }

    @Override
    public char getUnicode() {
        return unicode;
    }
}
