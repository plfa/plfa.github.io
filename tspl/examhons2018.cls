 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% I N F O R M A T I C S
%  Honours Exam LaTeX Package v0.1
%
%  Created: 12-Oct-2009 by G.O.Passmore.
%  Last Updated: 11-07-2017 by G.Hall
%
%  Note: We are changing the file and package name of this style
%   from year to year, so as to make people aware of the version
%   they are using.  The format is `examhons<YYYY>.sty' with <YYYY>
%   replaced appropriately. 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\NeedsTeXFormat{LaTeX2e}[1995/12/01]
\ProvidesClass{examhons2016}[2009/10/12 v0.1 (GOP)]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Set the ITO path for status.tex.
%
% * Note that course organisers / exam preparers do not need 
%    status.tex.  When building their exam on their own machines, 
%    the exam title / date / etc. information will be automatically
%    filled-in with dummy values for mock-up purposes. 
% 
%    Once the exam document is processed on the ITO machines, 
%    however, the mock-up exam title / date / etc. data will be 
%    overwritten with the officially sanctioned data held in 
%    the ITO's master status.tex file.
%
%  This file resides in the relative path below.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\itostatuspath{../exam-macros/}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Inherit the proper letter class.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\LoadClass[12pt,a4paper]{article}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 
% Take care of `page x of y' the proper way, based on a combination 
%  of the J. Goldberg (lastpage) method, the C. Huggins (using fh)
%  code, woven together with some use of the ifthen package for 
%  branching on p0 (the exam title page, which shouldn't be num'd).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\RequirePackage{fancyhdr,ifthen,a4}
\pagestyle{fancy}
\fancyhf{}

\def\lastpage@putlabel{\addtocounter{page}{-1}%
   \immediate\write\@auxout{\string
   \newlabel{LastPage}{{}{\thepage}}}%
   \addtocounter{page}{1}}

\AtEndDocument{%
   \message{*** Setting LastPage: Make sure you 
     run LaTeX upon your exam file at least 3
     times to get this right.}%
   \clearpage\lastpage@putlabel}%

\newcommand{\totalpagesoverride}{0}

 {\rfoot{\ifthenelse{\totalpagesoverride=0}
          {\ifthenelse{\thepage>0}
           {\scriptsize{Page \thepage{} of \pageref{LastPage}}}
           {}}
          {{\scriptsize{Page \thepage{} of \@forcedtotalpages}}}}}


\renewcommand\headrulewidth{0pt}  

\newcommand{\settotalpages}[1]{
 \def\@forcedtotalpages{#1}
 \renewcommand{\totalpagesoverride}{1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Inlining of the EPSF package by Rokicki et al.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newread\epsffilein    % file to \read
\newif\ifepsffileok    % continue looking for the bounding box?
\newif\ifepsfbbfound   % success?
\newif\ifepsfverbose   % report what you're making?
\newif\ifepsfdraft     % use draft mode?
\newdimen\epsfxsize    % horizontal size after scaling
\newdimen\epsfysize    % vertical size after scaling
\newdimen\epsftsize    % horizontal size before scaling
\newdimen\epsfrsize    % vertical size before scaling
\newdimen\epsftmp      % register for arithmetic manipulation
\newdimen\pspoints     % conversion factor
%
\pspoints=1bp          % Adobe points are `big'
\epsfxsize=0pt         % Default value, means `use natural size'
\epsfysize=0pt         % ditto
%
\def\epsfbox#1{\global\def\epsfllx{72}\global\def\epsflly{72}%
   \global\def\epsfurx{540}\global\def\epsfury{720}%
   \def\lbracket{[}\def\testit{#1}\ifx\testit\lbracket
   \let\next=\epsfgetlitbb\else\let\next=\epsfnormal\fi\next{#1}}%
%
\def\epsfgetlitbb#1#2 #3 #4 #5]#6{\epsfgrab #2 #3 #4 #5 .\\%
   \epsfsetgraph{#6}}%
%
\def\epsfnormal#1{\epsfgetbb{#1}\epsfsetgraph{#1}}%
%
\def\epsfgetbb#1{%
%
%   The first thing we need to do is to open the
%   PostScript file, if possible.
%
\openin\epsffilein=#1
\ifeof\epsffilein\errmessage{I couldn't open #1, will ignore it}\else
%
%   Okay, we got it. Now we'll scan lines until we find one that doesn't
%   start with %. We're looking for the bounding box comment.
%
   {\epsffileoktrue \chardef\other=12
    \def\do##1{\catcode`##1=\other}\dospecials \catcode`\ =10
    \loop
       \read\epsffilein to \epsffileline
       \ifeof\epsffilein\epsffileokfalse\else
%
%   We check to see if the first character is a % sign;
%   if not, we stop reading (unless the line was entirely blank);
%   if so, we look further and stop only if the line begins with
%   `%%BoundingBox:'.
%
          \expandafter\epsfaux\epsffileline:. \\%
       \fi
   \ifepsffileok\repeat
   \ifepsfbbfound\else
    \ifepsfverbose\message{No bounding box comment in #1; using defaults}\fi\fi
   }\closein\epsffilein\fi}%
%
%   Now we have to calculate the scale and offset values to use.
%   First we compute the natural sizes.
%
\def\epsfclipon{\def\epsfclipstring{ clip}}%
\def\epsfclipoff{\def\epsfclipstring{\ifepsfdraft\space clip\fi}}%
\epsfclipoff
%
\def\epsfsetgraph#1{%
   \epsfrsize=\epsfury\pspoints
   \advance\epsfrsize by-\epsflly\pspoints
   \epsftsize=\epsfurx\pspoints
   \advance\epsftsize by-\epsfllx\pspoints
%
%   If `epsfxsize' is 0, we default to the natural size of the picture.
%   Otherwise we scale the graph to be \epsfxsize wide.
%
   \epsfxsize\epsfsize\epsftsize\epsfrsize
   \ifnum\epsfxsize=0 \ifnum\epsfysize=0
      \epsfxsize=\epsftsize \epsfysize=\epsfrsize
      \epsfrsize=0pt
%
%   We have a sticky problem here:  TeX doesn't do floating point arithmetic!
%   Our goal is to compute y = rx/t. The following loop does this reasonably
%   fast, with an error of at most about 16 sp (about 1/4000 pt).
% 
     \else\epsftmp=\epsftsize \divide\epsftmp\epsfrsize
       \epsfxsize=\epsfysize \multiply\epsfxsize\epsftmp
       \multiply\epsftmp\epsfrsize \advance\epsftsize-\epsftmp
       \epsftmp=\epsfysize
       \loop \advance\epsftsize\epsftsize \divide\epsftmp 2
       \ifnum\epsftmp>0
          \ifnum\epsftsize<\epsfrsize\else
             \advance\epsftsize-\epsfrsize \advance\epsfxsize\epsftmp \fi
       \repeat
       \epsfrsize=0pt
     \fi
   \else \ifnum\epsfysize=0
     \epsftmp=\epsfrsize \divide\epsftmp\epsftsize
     \epsfysize=\epsfxsize \multiply\epsfysize\epsftmp   
     \multiply\epsftmp\epsftsize \advance\epsfrsize-\epsftmp
     \epsftmp=\epsfxsize
     \loop \advance\epsfrsize\epsfrsize \divide\epsftmp 2
     \ifnum\epsftmp>0
        \ifnum\epsfrsize<\epsftsize\else
           \advance\epsfrsize-\epsftsize \advance\epsfysize\epsftmp \fi
     \repeat
     \epsfrsize=0pt
    \else
     \epsfrsize=\epsfysize
    \fi
   \fi
%
%  Finally, we make the vbox and stick in a \special that dvips can parse.
%
   \ifepsfverbose\message{#1: width=\the\epsfxsize, height=\the\epsfysize}\fi
   \epsftmp=10\epsfxsize \divide\epsftmp\pspoints
   \vbox to\epsfysize{\vfil\hbox to\epsfxsize{%
      \ifnum\epsfrsize=0\relax
        \special{PSfile=\ifepsfdraft psdraft.ps\else#1\fi\space
             llx=\epsfllx\space lly=\epsflly\space
             urx=\epsfurx\space ury=\epsfury\space rwi=\number\epsftmp
             \epsfclipstring}%
      \else
        \epsfrsize=10\epsfysize \divide\epsfrsize\pspoints
        \special{PSfile=\ifepsfdraft psdraft.ps\else#1\fi\space
             llx=\epsfllx\space lly=\epsflly\space
             urx=\epsfurx\space ury=\epsfury\space rwi=\number\epsftmp\space
             rhi=\number\epsfrsize \epsfclipstring}%
      \fi
      \hfil}}%
\global\epsfxsize=0pt\global\epsfysize=0pt}%
%
%   We still need to define the tricky \epsfaux macro. This requires
%   a couple of magic constants for comparison purposes.
%
{\catcode`\%=12 \global\let\epsfpercent=%\global\def\epsfbblit{%BoundingBox}}%
%
%   So we're ready to check for `%BoundingBox:' and to grab the
%   values if they are found.
%
\long\def\epsfaux#1#2:#3\\{\ifx#1\epsfpercent
   \def\testit{#2}\ifx\testit\epsfbblit
      \epsfgrab #3 . . . \\%
      \epsffileokfalse
      \global\epsfbbfoundtrue
   \fi\else\ifx#1\par\else\epsffileokfalse\fi\fi}%
%
%   Here we grab the values and stuff them in the appropriate definitions.
%
\def\epsfempty{}%
\def\epsfgrab #1 #2 #3 #4 #5\\{%
\global\def\epsfllx{#1}\ifx\epsfllx\epsfempty
      \epsfgrab #2 #3 #4 #5 .\\\else
   \global\def\epsflly{#2}%
   \global\def\epsfurx{#3}\global\def\epsfury{#4}\fi}%
%
%   We default the epsfsize macro.
%
\def\epsfsize#1#2{\epsfxsize}
%
%   Finally, another definition for compatibility with older macros.
%
\let\epsffile=\epsfbox


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Inlining of the UK date package by A. Clark.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\@cent{\count0 }                      
\def\@diy{\count1 }                        
\def\@dow{\count2 }                        
\def\@epact{\count3 }                      
\def\@golden{\count4 }                     
\def\@leap{\count5 }                       
\def\@x{\count6 }                          
\def\@y{\count7 }                          

\def\@up#1{{\@savestyle\thinspace$^{\underline{\hbox{%
  \scriptsize\@setstyle#1\fam=-1 }}}$}}
\def\st{\@up{st}}
\def\nd{\@up{nd}}
\def\rd{\@up{rd}}
\def\th{\@up{th}}

\def\@savestyle{\count0=\the\fam}
\def\@setstyle{\ifcase\count0\rm\or\mit\or\cal\or\rm
  \or\it\or\sl\or\bf\or\tt\fi}

\def\today{\dayofweek{} \number\day\ifcase\day
  \or\st\or\nd\or\rd\or\th\or\th\or\th\or\th\or\th\or\th\or\th
  \or\th\or\th\or\th\or\th\or\th\or\th\or\th\or\th\or\th\or\th
  \or\st\or\nd\or\rd\or\th\or\th\or\th\or\th\or\th\or\th\or\th\or\st\fi
  \space\ifcase\month\or January\or February\or March\or April\or May\or
  June\or July\or August\or September\or October\or November\or December\fi
  \space\number\year}

\def\dayofweek{{%
  \@leap=\month \advance\@leap by -14 \divide\@leap by 12
  \advance\@leap by \year
  \@dow=\month \advance\@dow by 10
  \@y=\@dow \divide\@y by 13 \multiply\@y by 12
  \advance\@dow by -\@y \multiply\@dow by 13 
  \advance\@dow by -1 \divide\@dow by 5
  \advance\@dow by \day \advance\@dow by 77
  \@x=\@leap \@y=\@x \divide\@y by 100 \multiply\@y by 100 \advance\@x by -\@y
  \multiply\@x by 5 \divide\@x by 4 \advance\@dow by \@x
  \@x=\@leap \divide\@x by 400 \advance\@dow by \@x
  \@x=\@leap \divide\@x by 100 \multiply\@x by 2 \advance\@dow by -\@x
  \@x=\@dow \divide\@x by 7 \multiply\@x by 7 \advance\@dow by -\@x
  \ifcase\@dow Sunday\or Monday\or Tuesday\or Wednesday\or
      Thursday\or Friday\or Saturday\fi}}
\def\phaseofmoon{{%
  \@diy=\day \advance\@diy by \ifcase\month            
      -1\or -1\or 30\or 58\or 89\or 119\or 150\or      
      180\or 211\or 241\or 272\or 303\or 333\fi        
  \ifnum \month>2
    \@x=\year \@y=\@x \divide\@y by 4 \multiply\@y by 4 \advance\@x by -\@y
    \ifnum \@x=0                    
      \@x=\year \@y=\@x \divide\@y by 400 
      \multiply\@y by 400 \advance\@x by -\@y
      \ifnum \@x=0                  
      \advance\@diy by 1            
      \else                         
      \@x=\year \@y=\@x \divide\@y by 100 
      \multiply\@y by 100 \advance\@x by -\@y
      \ifnum \@x>0                  
          \advance\@diy by 1        
      \fi                           
      \fi                           
    \fi                             
  \fi                               
  \@cent=\year \divide\@cent by 100 \advance\@cent by 1
  \@golden=\year
  \@y=\year \divide\@y by 19 \multiply\@y by 19 \advance\@golden by -\@y
  \advance\@golden by 1
  \@epact=11 \multiply\@epact by \@golden
  \advance\@epact by 20
  \@x=8 \multiply\@x by \@cent \advance\@x by 5
  \divide\@x by 25 \advance\@x by -5
  \advance\@epact by \@x
  \@x=3 \multiply\@x by \@cent \divide\@x by 4 \advance\@x by -12
  \advance\@epact by -\@x
  \@y=\@epact \divide\@y by 30 \multiply\@y by 30 \advance\@epact by -\@y
  \ifnum \@epact<0
    \advance\@epact by 30
  \fi
  \ifnum \@epact=25
    \ifnum \@golden>11
      \advance \@epact by 1
    \fi
  \else
    \ifnum \@epact=24
      \advance \@epact by 1
    \fi
  \fi
  \@x=\@diy \advance\@x by \@epact \multiply\@x by 6 \advance\@x by 11
  \@y=\@x \divide\@y by 177 \multiply\@y by 177 \advance\@x by -\@y
  \divide\@x by 22
  \ifcase\@x new\or waxing crescent\or in its first quarter\or
      waxing gibbous\or full\or waning gibbous\or
      in its last quarter\or waning crescent\or new\fi}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Now, we want to define commands for exam title, time, conveners,
%  and so on, *but* we want to provide hard-coded dummy values
%  for exam preparers who are working on their own machines.
%  This is so that status.tex does not need to be ever copied from
%  the ITO installation; it is only for ITO.  
%
% The logic here is simple.  If we find \itostatuspath status.tex
%  to exist, then we populate the values of exam title, time, and
%  so on using those it contains corresponding to \courseid, which
%  is set by the exam preparer using the \setcourse command.
%  This is done internally by executing a command named 
%  \<courseid>details, with <courseid> replaced by their courseid.
%
% Otherwise, we use dummy values, but we've gone to the effort to
%  at least include the correct course title and type (Inf3,MSc,..)
%  within these mock values so as to keep the preparer happy ;-).
%
% Once that's done, we need to work out the rubric.  The rubric
%  is printed on the title page and is set by the exam author
%  using the \setrubric command.  They have the following options:
%
%   {qu1_and_either_qu2_or_qu3, any_two_of_three, custom}.
%
% Again, the usage of this information follows the same structure
%  as above.  On an ITO machine, the master files are sourced from
%  the itostatuspath directory.  On an exam preparer's machine,
%  we generate mock-up values for the rubric form and type.
%
% Note, if they create a custom rubric, they must then execute:
%
%  \setrubricform{} and \setrubrictype to specify the custom
%   rubric information.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\coursestatusfcn}{}
\newcommand{\courseid}{}
\newcommand{\rubricid}{}
\newcommand{\rubricform}{}
\newcommand{\rubrictype}{}

\providecommand{\status}{}

\newcommand{\setcourse}[1]{
 \renewcommand{\courseid}{#1}
}

\newcommand{\setrubric}[1]{\renewcommand{\rubricid}{#1}}
\newcommand{\setrubricform}[1]{\renewcommand{\rubricform}{#1}}
\newcommand{\setrubrictype}[1]{\renewcommand{\rubrictype}{#1}}

\AtBeginDocument{
 \newcounter{Day}   \setcounter{Day}{\day}
 \newcounter{Month} \setcounter{Month}{\month}
 \newcounter{Year}  \setcounter{Year}{\year}
}

\newenvironment{hint}{\par[{\bf Hint:} }{\nolinebreak]}
\newenvironment{hints}{\par[{\bf Hints:} }{\nolinebreak]}
\newenvironment{note}{\par[{\bf Note:} }{\nolinebreak]}
\newenvironment{notes}{\par[{\bf Notes:} }{\nolinebreak]}

\def\ps@header{\let\@mkboth\@gobbletwo
     \let\@oddfoot\@empty\let\@evenhead\@empty\let\@evenfoot\@oddfoot}
\def\setstatus#1{\def\@status{#1}}
\def\@status{}
\def\@nextone{f}\def\@nextbutone{f}%
\def\@oddhead{{\bf\it \@status}\hfil\it\@conthead}
\def\@conthead{\if\@nextone t\relax QUESTION CONTINUED FROM PREVIOUS PAGE\fi\xdef\@nextone{\@nextbutone}\gdef\@nextbutone{f}}
\def\continued{%
\gdef\@nextbutone{t}
\par\rightline{\it QUESTION CONTINUES ON NEXT PAGE}\newpage%
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Display the exam status (for `internal'/`external' scrutiny, or 
%  `final' which will print no corresponding notice).
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\internal{
  \setstatus{\it FOR INTERNAL SCRUTINY (date of this version: \theDay/\theMonth/\theYear)}}
\def\external{
  \setstatus{\it FOR EXTERNAL EXAMINER (date of this version: \theDay/\theMonth/\theYear)}}
\def\final{\setstatus{}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Setup the proper marks displays.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\Marks#1#2{\marginpar{\raisebox{#2\baselineskip}{[{\it #1 
  \ifnum #1=1 mark\else marks\fi\/}]}}}
%Version for most situations.
\def\marks#1{\Marks{#1}{0}}
% The next version is to get around the problem that you cannot put a 
% marginpar in maths display.  Put \marksl just before the display line.
\def\marksd#1{\Marks{#1}{-2}}
% As above but raises the box.
\def\marksu#1{\Marks{#1}{1}}

\leftmargini=0pt

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% EPS macros by KK.
%
% The first argument is the filename and the second the size (of the 
%  x-axis or the y-axis respectively.  
%
% For example \psfigx{graph1.epsf}{5in} will input your first graph 
%  and make the x-axis equal to 4.5in, with the y-axis appropriately
%  scaled.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\psfigx#1#2{
  \begin{center}
     \leavevmode
     \epsfxsize=#2
     \epsffile{#1}
   \end{center}}
   
\def\psfigy#1#2{
  \begin{center}
     \leavevmode
     \epsfysize=#2
     \epsffile{#1}
   \end{center}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Commands for manipulating exam course data.
%
% We will use them to assign dummy values on exam preparer machines,
%  and otherwise will source the master ITO status.tex if it exists
%  (e.g., when we are compiling on an ITO machine).
%
% Also, the papertype.inc files and rubric.inc files will be 
%  loaded if we are on an ITO machine.  Otherwise, we will provide
%  dummy mock-up values for those as well.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand\papertitle[1]{\global\def\nameofpaper{\uppercase{#1}}}
\newcommand\papertype[1]{\global\def\typeofpaper{
 \InputIfFileExists{\itostatuspath #1}{}
  { 
    %
    % If we're here, then this is running on exam preparer's
    % machine.  So, we will use mock-up values for the exam
    % type text corresponding to #1.
    %
    % Options for #1 are {msc.inc, inf4msc.inc, inf3.inc, inf4.inc,
    %                     nonhons.inc}.
    %

   \ifthenelse{\equal{#1}{msc.inc}}
     {MSc Courses
       \vskip 0.1in
      Convener: ITO-Will-Determine\\
      External Examiners: ITO-Will-Determine}{}
   \ifthenelse{\equal{#1}{inf4msc.inc}}
     {Year 4 Courses
       \vskip 0.1in
      Convener: ITO-Will-Determine\\
      External Examiners: ITO-Will-Determine
       \vskip 0.5in
      MSc Courses
       \vskip 0.1in
      Convener: ITO-Will-Determine\\
      External Examiners: ITO-Will-Determine}{}
   \ifthenelse{\equal{#1}{inf3inf4.inc}}
     {Year 3 Courses
       \vskip 0.1in
      Convenor: ITO-Will-Determine\\
      External Examiners: ITO-Will-Determine
       \vskip 0.5in
      Year 4 Courses
       \vskip 0.1in
      Convener: ITO-Will-Determine\\
      External Examiners: ITO-Will-Determine}{}
   \ifthenelse{\equal{#1}{inf3.inc}}
     {Year 3 Courses
       \vskip 0.1in
      Convener: ITO-Will-Determine\\
      External Examiners: ITO-Will-Determine}{}
   \ifthenelse{\equal{#1}{inf4.inc}}
     {Year 4 Courses
       \vskip 0.1in
      Convener: ITO-Will-Determine\\
      External Examiners: ITO-Will-Determine}{}
   \ifthenelse{\equal{#1}{nonhons}}
     {\vskip 0.2in
      Convener: ITO-Will-Determine\\
      External Examiner: ITO-Will-Determine}{}}}}

\newcommand{\paperdate}[3]{\global\def\day{#1}\global\def\month{#2}\global\def\year{#3}}
\newcommand{\papertimes}[2]{\global\def\timeofpaper{#1 to #2}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Now, we first see if we're on an ITO machine and can load the 
%  proper status.tex.  If so, we do it and execute the corresponding
%  \coursestatusfcn.  
%
% Otherwise, based upon the value of courseid, we need to populate  
%  the title and type with basic mock-up data.
%
% This command must be called in the top-level exam document, after
%  the courseid has been set.
%
% To do so: \initcoursedata
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newcommand{\initcoursedata}{
 \IfFileExists{\itostatuspath status.tex}
  {
   %
   % If we're here, then we're on an ITO machine.
   %

   \input{\itostatuspath status.tex}

   %
   % We've loaded status.tex properly then, and can now execute
   %  the corresponding \XXXdetails command.
   %

    \ifthenelse{\equal{\courseid}{anlp}}
      {\anlpdetails}{}
    \ifthenelse{\equal{\courseid}{aleone}} 
      {\aleonedetails}{}
	\ifthenelse{\equal{\courseid}{adbs}} 
      {\adbsdetails}{}
    \ifthenelse{\equal{\courseid}{av}}
      {\avdetails}{}
	\ifthenelse{\equal{\courseid}{apl}}
      {\apldetails}{}
    \ifthenelse{\equal{\courseid}{abs}}
      {\absdetails}{}
    \ifthenelse{\equal{\courseid}{agta}}
      {\agtadetails}{}
    \ifthenelse{\equal{\courseid}{ads}}
      {\adsdetails}{}
	\ifthenelse{\equal{\courseid}{ad}}
	  {\addetails}{}
    \ifthenelse{\equal{\courseid}{ar}}
      {\ardetails}{}
    \ifthenelse{\equal{\courseid}{asr}}
      {\asrdetails}{}
    \ifthenelse{\equal{\courseid}{bioone}}
      {\bioonedetails}{}
    \ifthenelse{\equal{\courseid}{biotwo}}
      {\biotwodetails}{}
    \ifthenelse{\equal{\courseid}{bdl}}
      {\bdldetails}{}
	 \ifthenelse{\equal{\courseid}{cqi}}
      {\cqidetails}{}
    \ifthenelse{\equal{\courseid}{copt}}
      {\coptdetails}{}
    \ifthenelse{\equal{\courseid}{ct}}
      {\ctdetails}{}
    \ifthenelse{\equal{\courseid}{ccs}}
      {\ccsdetails}{}
    \ifthenelse{\equal{\courseid}{cmc}}
      {\cmcdetails}{}
    \ifthenelse{\equal{\courseid}{ca}}
      {\cadetails}{}
    \ifthenelse{\equal{\courseid}{cav}}
      {\cavdetails}{}
    \ifthenelse{\equal{\courseid}{car}}
      {\cardetails}{}
    \ifthenelse{\equal{\courseid}{comn}}
      {\comndetails}{}
    \ifthenelse{\equal{\courseid}{cd}}
      {\cddetails}{}
    \ifthenelse{\equal{\courseid}{cg}}
      {\cgdetails}{}
    \ifthenelse{\equal{\courseid}{cn}}
      {\cndetails}{}
    \ifthenelse{\equal{\courseid}{cp}}
      {\cpdetails}{}
    \ifthenelse{\equal{\courseid}{cs}}
      {\csdetails}{}
	\ifthenelse{\equal{\courseid}{dme}}
	  {\dmedetails}{}
	\ifthenelse{\equal{\courseid}{dds}}
	  {\ddsdetails}{}
    \ifthenelse{\equal{\courseid}{dbs}}
      {\dbsdetails}{}
    \ifthenelse{\equal{\courseid}{dmmr}}
      {\dmmrdetails}{}
    \ifthenelse{\equal{\courseid}{dmr}}
      {\dmrdetails}{}	  
    \ifthenelse{\equal{\courseid}{ds}}
      {\dsdetails}{}
	\ifthenelse{\equal{\courseid}{epl}}
	  {\epldetails}{}
    \ifthenelse{\equal{\courseid}{es}}
      {\esdetails}{}
    \ifthenelse{\equal{\courseid}{exc}}
      {\excdetails}{}
    \ifthenelse{\equal{\courseid}{fv}}
      {\fvdetails}{}
    \ifthenelse{\equal{\courseid}{fnlp}}
      {\fnlpdetails}{}
    \ifthenelse{\equal{\courseid}{hci}}
      {\hcidetails}{}
    \ifthenelse{\equal{\courseid}{infonecg}}
      {\infonecgdetails}{}
    \ifthenelse{\equal{\courseid}{infonecl}}
      {\infonecldetails}{}
    \ifthenelse{\equal{\courseid}{infoneda}}
      {\infonedadetails}{}
    \ifthenelse{\equal{\courseid}{infonefp}}
      {\infonefpdetails}{}
    \ifthenelse{\equal{\courseid}{infonefpam}}
      {\infonefpamdetails}{}
    \ifthenelse{\equal{\courseid}{infonefppm}}
      {\infonefppmdetails}{}
    \ifthenelse{\equal{\courseid}{infoneop}}
      {\infoneopdetails}{}
    \ifthenelse{\equal{\courseid}{infoneopam}}
      {\infoneopamdetails}{}
    \ifthenelse{\equal{\courseid}{infoneoppm}}
      {\infoneoppmdetails}{}
    \ifthenelse{\equal{\courseid}{inftwoa}}
      {\inftwoadetails}{}
    \ifthenelse{\equal{\courseid}{inftwob}}
      {\inftwobdetails}{}
    \ifthenelse{\equal{\courseid}{inftwoccs}}
      {\inftwoccsdetails}{}
    \ifthenelse{\equal{\courseid}{inftwocse}}
      {\inftwocsedetails}{}
    \ifthenelse{\equal{\courseid}{inftwod}}
      {\inftwoddetails}{}
    \ifthenelse{\equal{\courseid}{iar}}
      {\iardetails}{}
    \ifthenelse{\equal{\courseid}{imc}}
      {\imcdetails}{}
    \ifthenelse{\equal{\courseid}{iotssc}}
      {\iotsscdetails}{}	  
    \ifthenelse{\equal{\courseid}{iqc}}
      {\iqcdetails}{}
    \ifthenelse{\equal{\courseid}{itcs}}
      {\itcsdetails}{}
    \ifthenelse{\equal{\courseid}{ivc}}
      {\ivcdetails}{}	  
    \ifthenelse{\equal{\courseid}{ivr}}
      {\ivrdetails}{}
    \ifthenelse{\equal{\courseid}{iaml}}
      {\iamldetails}{}
    \ifthenelse{\equal{\courseid}{lpt}}
      {\lptdetails}{}
    \ifthenelse{\equal{\courseid}{lpp}}
      {\lppdetails}{}
    \ifthenelse{\equal{\courseid}{mlpr}}
      {\mlprdetails}{}
    \ifthenelse{\equal{\courseid}{mt}}
      {\mtdetails}{}
	\ifthenelse{\equal{\courseid}{mi}}
	  {\midetails}{}
    \ifthenelse{\equal{\courseid}{nlu}} 
      {\nludetails}{}
    \ifthenelse{\equal{\courseid}{nc}} 
      {\ncdetails}{}
    \ifthenelse{\equal{\courseid}{nip}}
      {\nipdetails}{}
    \ifthenelse{\equal{\courseid}{os}}
      {\osdetails}{}
    \ifthenelse{\equal{\courseid}{pa}}
      {\padetails}{}
    \ifthenelse{\equal{\courseid}{pdiot}}
      {\pdiotdetails}{}	  
    \ifthenelse{\equal{\courseid}{ppls}}
      {\pplsdetails}{}
    \ifthenelse{\equal{\courseid}{pm}}
      {\pmdetails}{}
    \ifthenelse{\equal{\courseid}{pmr}}
      {\pmrdetails}{}
    \ifthenelse{\equal{\courseid}{pi}}
      {\pidetails}{}
    \ifthenelse{\equal{\courseid}{rc}}
      {\rcdetails}{}
    \ifthenelse{\equal{\courseid}{rl}}
      {\rldetails}{}
    \ifthenelse{\equal{\courseid}{rlsc}}
      {\rlscdetails}{}
    \ifthenelse{\equal{\courseid}{rss}}
      {\rssdetails}{}
	\ifthenelse{\equal{\courseid}{sp}}
	  {\spdetails}{}
    \ifthenelse{\equal{\courseid}{sws}}
      {\swsdetails}{}
	\ifthenelse{\equal{\courseid}{stn}}
	  {\stndetails}{}
    \ifthenelse{\equal{\courseid}{sapm}}
      {\sapmdetails}{}
    \ifthenelse{\equal{\courseid}{sdm}}
      {\sdmdetails}{}
    \ifthenelse{\equal{\courseid}{st}}
      {\stdetails}{}
    \ifthenelse{\equal{\courseid}{ttds}}
      {\ttdsdetails}{}
    \ifthenelse{\equal{\courseid}{tspl}}
      {\tspldetails}{}

  }
  { 
   %
   % If we're here, then we're on an exam preparer's machine.
   % So, we're going to use their set \courseid to give some
   %  nice mock-up values to the title and type text.
   %
  
    \ifthenelse{\equal{\courseid}{anlp}}
      {\papertitle{INFR 11125 Accelerated Natural Language Processing}
       \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{aleone}}
      {\papertitle{Adaptive Learning Environments (Level 11)}
       \papertype{inf4.inc}}{}
	\ifthenelse{\equal{\courseid}{adbs}}
      {\papertitle{Advanced Databases}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{av}}
      {\papertitle{Advanced Vision (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{apl}}
      {\papertitle{Advances in Programming Languages}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{abs}}
      {\papertitle{Agent Based Systems}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{agta}}
      {\papertitle{Algorithmic Game Theory and its Applications}
       \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{ads}}
      {\papertitle{Algorithms and Data Structures}
       \papertype{inf3.inc}}{}
	\ifthenelse{\equal{\courseid}{ad}}
	  {\papertitle{INFR11015 Applied Databases}
	   \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{ar}}
      {\papertitle{Automated Reasoning (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{asr}}
      {\papertitle{Automatic Speech Recognition}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{bioone}}
      {\papertitle{Bioinformatics 1}
       \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{biotwo}}
      {\papertitle{Bioinformatics 2}
       \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{bdl}}
      {\papertitle{INFR11144 Blockchains and Distributed Ledgers}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{cqi}}
      {\papertitle{Categories and Quantum Informatics}
       \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{copt}}
      {\papertitle{Compiler Optimisation (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{ct}}
      {\papertitle{Compiling Techniques}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{ccs}}
      {\papertitle{Computational Cognitive Science}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{cmc}}
      {\papertitle{Computational Complexity}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{ca}}
      {\papertitle{Computer Algebra}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{cav}}
      {\papertitle{Computer Animation and Visualisation (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{car}}
      {\papertitle{Computer Architecture}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{comn}}
      {\papertitle{Computer Communications and Networks}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{cd}}
      {\papertitle{Computer Design}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{cg}}
      {\papertitle{Computer Graphics (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{cn}}
      {\papertitle{Computer Networking (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{cp}}
      {\papertitle{Computer Programming Skills and Concepts}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{cs}}
      {\papertitle{Computer Security}
       \papertype{inf3.inc}}{}
	\ifthenelse{\equal{\courseid}{dds}}
	  {\papertitle{INFR08024 Data, Design and Society}
	   \papertype{nonhons.inc}}{}
	\ifthenelse{\equal{\courseid}{dme}}
	  {\papertitle{Data Mining and Exploration}
	   \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{dbs}}
      {\papertitle{Database Systems}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{dmr}}
      {\papertitle{Decision Making in Robots and Autonomous Agents}
       \papertype{nonhons.inc}}{}	   
    \ifthenelse{\equal{\courseid}{dmmr}}
      {\papertitle{Discrete Mathematics and Mathematical Reasoning}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{ds}}
      {\papertitle{Distributed Systems (Level 11)}
       \papertype{inf4.inc}}{}
	\ifthenelse{\equal{\courseid}{epl}}
	  {\papertitle{INFR10061 Elements of Programming Languages}
	   \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{es}}
      {\papertitle{Embedded Software}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{exc}}
      {\papertitle{Extreme Computing}
       \papertype{inf4.inc}}{}
	\ifthenelse{\equal{\courseid}{fv}}
      {\papertitle{Formal Verification}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{fnlp}}
      {\papertitle{Foundations of Natural Language Processing}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{hci}}
      {\papertitle{Human-Computer Interaction (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{infonecg}}
      {\papertitle{Informatics 1 --- Cognitive Science}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{infonecl}}
      {\papertitle{Informatics 1 --- Computation \& Logic}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{infoneda}}
      {\papertitle{Informatics 1 --- Data \& Analysis}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{infonefp}}
      {\papertitle{Informatics 1 --- Functional Programming}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{infonefpam}}
      {\papertitle{Informatics 1 --- Functional Programming}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{infonefppm}}
      {\papertitle{Informatics 1 --- Functional Programming}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{infoneop}}
      {\papertitle{Informatics 1 --- Object-Oriented Programming}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{infoneopam}}
      {\papertitle{Informatics 1 --- Object-Oriented Programming}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{infoneoppm}}
      {\papertitle{Informatics 1 --- Object-Oriented Programming}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{inftwoa}}
      {\papertitle{Informatics 2A: Processing Formal and Natural Languages}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{inftwob}}
      {\papertitle{Informatics 2B: Algorithms, Data Structures, Learning}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{inftwoccs}}
      {\papertitle{Informatics 2C: Introduction to Computer Systems}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{inftwocse}}
      {\papertitle{Informatics 2C: Introduction to Software Engineering}
       \papertype{nonhons.inc}}{}
    \ifthenelse{\equal{\courseid}{inftwod}}
      {\papertitle{Informatics 2D: Reasoning and Agents}
       \papertype{nonhons.inc}}{}
  \ifthenelse{\equal{\courseid}{iar}}
       {\papertitle{Intelligent Autonomous Robotics (Level 10)}
       \papertype{inf4.inc}}{}
	\ifthenelse{\equal{\courseid}{imc}}
       {\papertitle{Introduction to Modern Cryptography}
       \papertype{inf4.inc}}{}
	\ifthenelse{\equal{\courseid}{iotssc}}
       {\papertitle{Internet of Things Systems, Security, and the Cloud}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{iqc}}
       {\papertitle{Introduction to Quantum Computing}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{itcs}}
       {\papertitle{Introduction to Theoretical Computer Science}
        \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{ivc}}
      {\papertitle{Image and Vision Computing}
       \papertype{msc.inc}}{}		
    \ifthenelse{\equal{\courseid}{ivr}}
      {\papertitle{Introduction to Vision and Robotics}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{iaml}}
      {\papertitle{Introductory Applied Machine Learning}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{lpt}}
      {\papertitle{Logic Programming --- Theory}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{lpp}}
      {\papertitle{Logic Programming --- Programming}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{mlpr}}
      {\papertitle{Machine Learning and Pattern Recognition}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{mt}}
      {\papertitle{Machine Translation (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{mi}}
      {\papertitle{INFR11079 Music Informatics}
       \papertype{msc.inc}}{}	  
    \ifthenelse{\equal{\courseid}{nlu}}
      {\papertitle{Natural Language Understanding (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{nc}}
      {\papertitle{Neural Computation}
       \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{nip}}
      {\papertitle{Neural Information Processing}
       \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{os}}
      {\papertitle{Operating Systems}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{pa}}
      {\papertitle{Parallel Architectures (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{pdiot}}
      {\papertitle{Principles and Design of IoT Systems}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{ppls}}
      {\papertitle{Parallel Programming Languages and Systems (Level 11)}
       \papertype{inf4.inc}}{}
	\ifthenelse{\equal{\courseid}{pm}}
      {\papertitle{Performance Modelling}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{pmr}}
      {\papertitle{Probabilistic Modelling and Reasoning}
       \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{pi}}
      {\papertitle{Professional Issues}
       \papertype{inf3.inc}}{}
	\ifthenelse{\equal{\courseid}{rc}}
      {\papertitle{Randomness and Computation}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{rl}}
      {\papertitle{Reinforcement Learning}
       \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{rlsc}}
      {\papetitle{Robot Learning and Sensorimotor Control}
       \papertype{msc.inc}}{}
    \ifthenelse{\equal{\courseid}{rss}}
      {\papertitle{Robotics: Science and Systems}
       \papertype{msc.inc}}{}
	\ifthenelse{\equal{\courseid}{sp}}
	  {\papertitle{INFR11098 Secure Programming}
	   \papertype{inf4.inc}}{}
	\ifthenelse{\equal{\courseid}{sws}}
	  {\papertitle{INFR11104 Semantic Web Systems}
	   \papertype{inf4.inc}}{}
	\ifthenelse{\equal{\courseid}{stn}}
	  {\papertitle{INFR11124 Social and Technological Networks}
	   \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{sapm}}
      {\papertitle{Software Architecture, Process and Management (Level 11)}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{sdm}}
      {\papertitle{Software Design and Modelling}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{st}}
      {\papertitle{Software Testing}
       \papertype{inf3.inc}}{}
    \ifthenelse{\equal{\courseid}{ttds}}
      {\papertitle{Text Technologies for Data Science}
       \papertype{inf4.inc}}{}
    \ifthenelse{\equal{\courseid}{tspl}}
      {\papertitle{Types and Semantics for Programming Languages}
       \papertype{inf4.inc}}{}

 %   \ifthenelse{\equal{\courseid}{XXX}}
 %     { }{}

 %
 % Let's also do a mock-up date/time to make the exam preparer happy:
 % (Aren't we sweet?)
 %
  
    \paperdate{1}{4}{2017}
    \papertimes{00:00}{00:00}

 %
 % Also, we'll set the exam status to internal for the mock-up.
 %

    \internal

  }}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Now, we can build the appropriate rubric form and type.
%
% We set rubric type and form to alert values.  These will be over-
%  written if the author has done things right.  Otherwise, they
%  will provide good error messages to the author.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\setrubricform{Rubric Form has not been initialized.}
\setrubrictype{Rubric type has not been initialized.}

\newcommand{\initrubricdata}{

 %
 % We need to load both form and type data for the rubric.
 %
 % If we're on an ITO machine, we'll load it from the master path.
 % If not, we'll setup some mock-up values.
 %
 % We only do this if the rubric is not custom, though.
 %
 % This section also defines \rubricqA, B and C.  These are initialised as empty definitions
 % and then the correct text is added depending on the rubric selected
 %
 \def\rubricqA{}
 \def\rubricqB{}
 \def\rubricqC{}

 \ifthenelse{\equal{\rubricid}{custom}}{}
 {
     %% HONS RUBRICS
     
     \ifthenelse{\equal{\rubricid}{qu1_and_either_qu2_or_qu3}}{
     \setrubrictype{
         Answer QUESTION 1 and ONE other question. \\
          \bigskip
         Question 1 is COMPULSORY. If both QUESTION 2 and QUESTION 3 are answered, only QUESTION 2 will be marked. \\
          \bigskip
         All questions carry equal weight.\\
	      \bigskip
	     CALCULATORS MAY NOT BE USED IN THIS EXAMINATION \\
         }
         
         %% Additional command to be used for question 1.
         \def\rubricqA{THIS QUESTION IS COMPULSORY}
		 \def\rubricqB{ANSWER EITHER THIS QUESTION OR QUESTION 3}
		 \def\rubricqC{ANSWER EITHER THIS QUESTION OR QUESTION 2}
     }{}

     \ifthenelse{\equal{\rubricid}{qu1_and_either_qu2_or_qu3_calc}}{
     \setrubrictype{
         Answer QUESTION 1 and ONE other question. \\
	      \bigskip
	     Question 1 is COMPULSORY. If both QUESTION 2 and QUESTION 3 are answered, only QUESTION 2 will be marked. \\
	      \bigskip
	     All questions carry equal weight.\\
           \bigskip

         CALCULATORS MAY BE USED IN THIS EXAMINATION \\
         }
         
         %% Additional command to be used for question 1.
         \def\rubricqA{THIS QUESTION IS COMPULSORY}
		 \def\rubricqB{ANSWER EITHER THIS QUESTION OR QUESTION 3}
		 \def\rubricqC{ANSWER EITHER THIS QUESTION OR QUESTION 2}
     }{}

     \ifthenelse{\equal{\rubricid}{any_two_of_three}}{
     \setrubrictype{
         Answer any TWO of the three questions. If more than two questions are answered, only QUESTION 1 and QUESTION 2 will be marked.\\
          \bigskip
         All questions carry equal weight.\\
	      \bigskip
         CALCULATORS MAY NOT BE USED IN THIS EXAMINATION \\
         }
     }{}

     \ifthenelse{\equal{\rubricid}{any_two_of_three_calc}}{
     \setrubrictype{
	     Answer any TWO of the three questions. If more than two questions are answered, only QUESTION 1 and QUESTION 2 will be marked.\\
	      \bigskip
         All questions carry equal weight.\\
          \bigskip
         CALCULATORS MAY BE USED IN THIS EXAMINATION \\
         }
     }{}
       
     \ifthenelse{\equal{\rubricid}{infone}}{
     \setrubrictype{
	     \begin{enumerate}
	     \item Note that ALL QUESTIONS ARE COMPULSORY.
	     \item DIFFERENT QUESTIONS MAY HAVE DIFFERENT NUMBERS OF TOTAL MARKS.
	           Take note of this in allocating time to questions.
	     \item CALCULATORS MAY NOT BE USED IN THIS EXAMINATION.
	     \end{enumerate}
         }
     }{}

	 \ifthenelse{\equal{\rubricid}{infone_calcs}}{
     \setrubrictype{
	     \begin{enumerate}
         \item Note that ALL QUESTIONS ARE COMPULSORY.
         \item DIFFERENT QUESTIONS MAY HAVE DIFFERENT NUMBERS OF TOTAL MARKS.
               Take note of this in allocating time to questions.
         \item CALCULATORS MAY BE USED IN THIS EXAMINATION.
         \end{enumerate}
         }
     }{}

     \ifthenelse{\equal{\rubricid}{infone_openbook}}{
     \setrubrictype{
         \begin{enumerate}
         \item Note that ALL QUESTIONS ARE COMPULSORY.
         \item DIFFERENT QUESTIONS MAY HAVE DIFFERENT NUMBERS OF TOTAL MARKS.
               Take note of this in allocating time to questions.
         \item This is an OPEN BOOK examination: notes and printed material are allowed,
               but no electronic devices or electronic media.
         \end{enumerate}
         }
     }{}
	
 }
}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Now, we can build the title page.  This command must be called
%  from the top-level exam document.
%
% To do so: \examtitlepage 
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


\newcommand{\examtitlepage}{

\initrubricdata

\status

\thispagestyle{header}
\begin{center}
 {UNIVERSITY OF EDINBURGH}
 \vskip 0.1in
 {COLLEGE OF SCIENCE AND ENGINEERING}
 \vskip 0.1in
 {SCHOOL OF INFORMATICS}
 \vskip 0.5in

\begin{bf}
{\nameofpaper}

\begin{small}
\vskip 0.5in
{\today} \\
\vskip 0.2in
{\timeofpaper}
\vskip 0.75in
\end{small}

{INSTRUCTIONS TO CANDIDATES} \\
\bigskip\bigskip

\rubrictype
\end{bf}

\vskip 0.5in

\begin{small}
{\typeofpaper}
\end{small}

\vskip 0.5in
THIS EXAMINATION WILL BE MARKED ANONYMOUSLY

\end{center}

\setcounter{page}{0}
\newpage

\status
}


