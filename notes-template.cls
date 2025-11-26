\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{notes-template}

\PassOptionsToPackage{dvipsnames}{xcolor}

\PassOptionsToClass{titlepage=false}{scrartcl}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{scrartcl}} 

\ProcessOptions\relax

\LoadClass{scrartcl}

% Thème
%--------------------------------------------------------

\RequirePackage{fontspec}

\RequirePackage[a4paper]{geometry}

\setlength\parindent{10pt}

\setromanfont[
  BoldFont={Libertinus Serif Semibold}, BoldItalicFont={Libertinus Serif Semibold Italic}]
{Libertinus Serif}
% \setmonofont[BoldFont={Fira Code},
%   Contextuals={Alternate},Scale=MatchLowercase]{Fira Code Light}%
% \newfontfamily\firamath{Fira Code}[Scale=MatchLowercase]

\setsansfont{Libertinus Sans}
\renewcommand{\familydefault}{\sfdefault}

\RequirePackage{enumitem}
\setlist{nosep}
\setlist[description]{font=\itshape,labelindent=\parindent}

\RedeclareSectionCommand[beforeskip=.5\baselineskip plus 1sp minus -1sp]{paragraph}

% \RequirePackage[compact]{titlesec}
% \RequirePackage{titletoc}

% % Without a re-definition of all of them, there is an error?  
%   \titleformat{\section}
%     {\normalfont\Large\bfseries}{\thesection}{1em}{}

%   \titleformat{\subsection}
%     {\normalfont\large\bfseries}{\thesubsection}{1em}{}
%   \titleformat{\subsubsection}
%     {\normalfont\normalsize\bfseries}{\thesubsubsection}{1em}{}
  % \titleformat{\paragraph}[hang]
  %   {\normalfont\normalsize\bfseries}{\theparagraph}{1em}{}
%   \titleformat{\subparagraph}[hang]
%     {\normalfont\normalsize\bfseries\color{gray}}{\thesubparagraph}{1em}{}
%   \titlespacing*{\paragraph}{0pt}{3.25ex plus 1ex minus .2ex}{1ex plus .2ex}
%   \titlespacing*{\subparagraph}{0pt}{3.25ex plus 1ex minus .2ex}{1ex plus .2ex}


% Mathematical Fonts
% -----------------------------

\expandafter\let\csname not=\endcsname\relax
\expandafter\let\csname not<\endcsname\relax
\expandafter\let\csname not>\endcsname\relax

\RequirePackage{mathtools} % Should be loaded before unicode-math!
\RequirePackage{amssymb}
\RequirePackage{stmaryrd} % Needed for llbracket!

\RequirePackage[warnings-off={mathtools-colon,mathtools-overbracket}]{unicode-math}

\setmathfont{latinmodern-math.otf}

\setmathfontface\mathlin{Libertinus Math}[Scale=MatchLowercase]
\setmathfont{Libertinus Math}[Scale=MatchLowercase]
\setoperatorfont\mathlin

% % Reset the mathcal and blackboard bold to the ones from computer modern
%%  See https://tex.stackexchange.com/questions/127216/when-using-unicode-math-how-do-i-get-the-original-calligraphic-alphabet-back
%% and https://tex.stackexchange.com/questions/120065/xetex-what-happened-to-mathcal-and-mathscr
% \DeclareMathAlphabet{\mathcal}{OMS}{cmsy}{m}{n}
% \setmathfont[Scale=MatchLowercase,range=cal, StylisticSet=1]{XITS Math}
\setmathfont[Scale=MatchLowercase,range=bb]{Latin Modern Math}
\newfontfamily\checksymbol{DejaVu Sans} % because the checkmark is missing is Libertinus

% \setmathfont{XITS Math}[range={\smalltriangleright,\smallblacktriangleright,\mdwhtdiamond,\vbrtri}]

% Colors
% -------------------------------------------------------------

\RequirePackage[dvipsnames,svgnames]{xcolor}
%% Colors

\AtBeginDocument{\colorlet{defaultcolor}{.}}

% Linking
% ------------------------------------------------------

\RequirePackage{hyperref} % Required for hyperlinks

\urlstyle{same}
\hypersetup{ % Set up hyperref options
	unicode, % Use unicode for links
	pdfborder={0 0 0}, % Suppress border around pdf
	breaklinks=true,
	colorlinks=false}
  % citecolor=black,
  % filecolor=DarkGreen,
  % linkcolor=DarkGreen,
  % urlcolor=DarkBlue}
  % % To avoid colored links in math mode, see https://tex.stackexchange.com/questions/641422/knowledge-package-coloring
  % \everydisplay{\hypersetup{allcolors=.}}
  % \everymath{\hypersetup{allcolors=.}}

\RequirePackage[capitalize]{cleveref}

% Langue
% --------------------------------------------------------

\RequirePackage{csquotes}
\RequirePackage[french,english]{babel}
