%
% Makrodefinicje systemu SINOL
%
% \history{1.0}{Grzegorz Jakacki}{98/11/15}
% \history{1.1}{Grzegorz Jakacki}{99/11/28}
% \history{1.2}{Tomasz Walen}{00/09/14}
% \history{1.2.1}{Tomasz Walen --- nazwy plikow pisane sa malymi lit.}{01/03/23}
% \history{1.3}{Tomasz Waleñ --- lepsza obsluga obrazkow, przykladow, wiele trybów komentowania dokumentów }{01/04/02}
% \history{1.3.1}{Tomasz Waleñ --- drobne zmiany, dodanie sinolLang, logo BOI}
% \history{1.3.2}{Tomasz Waleñ --- dodanie trybu we/wyj}
% \history{1.4}{Marcin Kubica --- Dodanie ilo¶ci potrzebnej pamiêci \RAM. Dodanie rysunków do ca³ych przyk³adów \exampleimg.}
% \history{1.4.1}{Jakub Pawlewicz --- nie³adowanie klas babel i inputenc w wersji angielskiej}
% \history{1.5}{Marcin Kubica --- dostosowanie do potrzeb konkursów
% miêdzynarodowych (CEOI)}
% \history{1.6}{Marcin Kubica --- dostosowanie do potrzeb IOI'2005:
%   - opcja \iomode{otputonly}
%   - opcja \iomode{interactive}
%   - \pagestyle{fancy} dzia³a tak, jak na IOI
%   - polecenie \Country
%   - \includegraphics zamiast \epsffile}
% \history{1.7}{Adam Iwanicki --- zmiana w tresci przykladowej input na
%          verbatiminput, bo poprzednie polecenie nie zachowywalo jednak
%          enterow}
% \history{1.7.1}{Marcin Kubica --- poprawka w \@exampleputtogetherv
%          dostosowuj±ca do verbatiminput.
% \history(1.7.2}{Marcin Kubica --- zwiekszenie miejsca na tytul zadania, 
%          kosztem miejsca na nazwe kraju}
% \history(1.8}{Szymon Acedanski --- zwiekszenie miejsca na tekst,
%          zdecydowane zmniejszenie marginesow strony}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\NeedsTeXFormat{LaTeX2e}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\def\sinolVersion{1.8}
\ProvidesClass{sinol}[1998/09/14 System Informatyczny Olimpiady \sinolVersion]
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\RequirePackage[T1]{fontenc}
\RequirePackage{epsf}
\RequirePackage{graphicx}
\RequirePackage{pslatex}
\RequirePackage{ifpdf}
\RequirePackage{fancyheadings}
\RequirePackage[czech,croatian,german,english,polish]{babel}
\RequirePackage[pliso]{inputenc}
\RequirePackage{verbatim}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% rozmiar papieru
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% zmienne logiczne
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newif\ifsinolshortages \sinolshortagesfalse % niedoprecyzowania
\newif\ifsinolerrors  \sinolerrorsfalse % bledy
\newif\ifmetric  \metrictrue  % czy drukowac metryke
\newif\ifzawodnik \zawodnikfalse  % czy wersja dla zawodnika
\newif\ifsignaturedefed \signaturedefedfalse % czy zdefiniowano sygnature
\newif\ifdatedefed \datedefedfalse  % czy podano date
\newif\ifetapdefed \etapdefedfalse  % czy podano etap
\newif\ifdaydefed \daydefedfalse  % czy podano dzien
\newif\ifRAMdefed \RAMdefedfalse  % czy podano dostêpn± pamiêæ
\newif\iftimedefed \timedefedfalse % czy podano czas dzia³ania
\newif\ifDocVersiondefed % czy zdefiniowano wersjê dokumentu
\DocVersiondefedfalse    % (domy¶lnie nie)
\newif\ifCountrydefed \Countrydefedfalse % Czy zdefiniowano kraj
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% \?{<tekst>} --- niedoprecyzowanie
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand\?[1]{%
% w zaleznosci od wybranego stylu, komentarze moga sie pojawiac
% tuz po niejasnosci, jako przypis lub na koncu
  \def\@tempf{footnote}\def\@tempa{appendix}\def\@tempm{margin}%%
  \edef\@tempcstyle{\cstyle}%
  \if@minipage\def\@tempcstyle{inline}\fi%
  \ifx\@tempcstyle\@tempf%
%%%% uwagi jako przypisy
    \footnote{#1}% 
  \else%
    \ifx\@tempcstyle\@tempm%
%%%% uwagi na marginiesie
       \stepcounter{sinolCommentNumber}%
       $^\thesinolCommentNumber$%
       \marginpar{\raggedright \footnotesize $^\thesinolCommentNumber$#1}%
    \else%
       \ifx\@tempcstyle\@tempa%
%%%% tradycyjna uwaga bezpo¶rednio w tek¶cie
         \addComment{#1}%
       \else%
         {
         \tt
         [[[#1]]]
         }
       \fi%
    \fi%
  \fi%
  \global\sinolshortagestrue%
}
% komentarze do tre¶ci zadañ
%%%%%%%%%%%%%%%%%%%%%%%%%%
\def\cstyle{inline}
\newcounter{sinolCommentNumber}
\global\def\comments{}
\newcommand\commentStyle[1]{
  \edef\cstyle{#1}%
}
%
\newcommand\addComment[1]{%
\stepcounter{sinolCommentNumber}%
$^\thesinolCommentNumber$%
\edef\comments{\comments\par $^\thesinolCommentNumber$ #1}
}
% 
\newcommand\showComments{
  \def\@empty{}
  \ifx\comments\@empty\else
    \section{\sinolSNameUwagi}    
    \comments
  \fi
}
% uwaga do tre¶ci zadania
\renewcommand\comment[2]{%
  {\it \underline{#1}}
  \?{#2}
}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% rozwijajace \uppercase
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\def\ucase#1{\expandafter\uppercase\expandafter{#1}}
\def\lcase#1{\expandafter\lowercase\expandafter{#1}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% logo
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\def\LOGO{%
%  \leavevmode
%  \hbox{%
%    \vbox to 0pt{%
%      \vss
%      \hbox{%
%        \includegraphics[height=2cm]{\sinolContestLogo}
%      }%
%    }%
%  }%
}%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \ifundef{<makro>}{<jesli tak>}{<jesli nie>}
% --- wykonuje jeden z blokow, w zaleznosci od tego,
%     czy makro jest zdefiniowane
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\def\ifundef#1#2#3{
  \expandafter
  \ifx\csname #1\endcsname\relax
    #2
  \else
    #3
  \fi
}
\def\ifeq#1#2#3{%
  \edef\@tempeqa{#1}%
  \edef\@tempeqb{#2}%
  \ifx\@tempeqa\@tempeqb
    #3
  \fi
}
\def\ifneq#1#2#3{%
  \edef\@tempeqa{#1}%
  \edef\@tempeqb{#2}%
  \ifx\@tempeqa\@tempeqb\else
    #3
  \fi
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% numery plikow
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chardef\inffile=15 % plik wejsciowy (np. testy)
\chardef\errfile=14 % plik wyjsciowy
\chardef\tmpfile=13 % plik tymczasowy
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% dane do metryki
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\def\sinolHistory{}
\def\sinolSignature{}
\def\sinolDocVersion{}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \concludedecls --- uruchamiane po przeczytaniu deklaracji
% \concludetext --- uruchamiane po przeczytaniu tekstu
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand{\concludedecls}{}
\newcommand{\concludetext}{}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% numer rozdzialu
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcount\sinolSectionNumber \sinolSectionNumber=0
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Footnote-ki indeksowane symbolami, a nie liczbami. 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\def\thefootnote{\fnsymbol{footnote}} 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \infoutput{<tekst>} --- wyprowadza do pliku informacyjnego
% \erroutput{<tekst>} --- wyprowadza do pliku z bledami
% \erroutputWrongSection{<jest>}{<winno byc>} --- wyprowadza
%   informacje o blednej nazwie rodzialu
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand{\infoutput}[1]{%
  \immediate\write\inffile{#1}
}

\newcommand{\erroutput}[1]{%
  \immediate\write\errfile{#1}
  \global\sinolerrorstrue
}

\newcommand{\erroutputWrongSection}[2]{%
  \erroutput{bledna nazwa lub lokalizacja rozdzialu '#1', spodziewane '#2'}%
}
%%
% obsluga obrazkow (TW, 2001.04.02)
%
%
\newlength{\imgwidth}
% podpis pod/nad obrazkiem
\newcommand\imgcaption[1]{%
\def\capwidth{\textwidth}%
\addtolength\capwidth{-1cm}%
\centerline{\begin{minipage}{\capwidth}\footnotesize #1\end{minipage}}%
}
%
% rysunek #1-plik, #2-podpis, #3-gdzie podpis (t-na gorze, b-na dole)
\newcommand\img[3]{%
\def\tmparg{#3}
\def\tmpb{b}
\setlength\imgwidth{\textwidth}%
\addtolength\imgwidth{-2cm}%
\begin{center}%
\begin{minipage}{\imgwidth}%
\ifx\tmparg\tmpb
  $$\includegraphics{#1}$$%
  \hrule%
  \smallskip%
  \imgcaption{#2}%
\else
  \imgcaption{#2}%
  \smallskip%
  \hrule%
  \smallskip%
  $$\includegraphics{#1}$$%
\fi
\end{minipage}\end{center}}
%
% rysunek z podpisem na gorze
\newcommand\timg[2]{\img{#1}{#2}{t}}
% rysunek z podpisem na dole
\newcommand\bimg[2]{\img{#1}{#2}{b}}
\newcommand\plainimg[1]{$\includegraphics{#1}$}
% tryb dwukolumnowy (kolumny -- #1 i #2) 
\newcommand\twocol[2]{%
\begin{center}%
\begin{minipage}[t]{0.5\textwidth}%
\vspace{0pt}%
{#1}%
\end{minipage}\hfill%
\begin{minipage}[t]{0.5\textwidth}%
\vspace{0pt}%
{#2}%
\end{minipage}%
\end{center}}
%
%
% Rozpoznawanie rysunków pochodz±cych z MetaPosta
\ifpdf
    \input supp-pdf.tex
    \input supp-mis.tex

    \DeclareGraphicsRule{.1}{mps}{*}{}
    \DeclareGraphicsRule{.2}{mps}{*}{}
    \DeclareGraphicsRule{.3}{mps}{*}{}
    \DeclareGraphicsRule{.4}{mps}{*}{}
    \DeclareGraphicsRule{.5}{mps}{*}{}
    \DeclareGraphicsRule{.6}{mps}{*}{}
    \DeclareGraphicsRule{.7}{mps}{*}{}
    \DeclareGraphicsRule{.8}{mps}{*}{}
    \DeclareGraphicsRule{.9}{mps}{*}{}
\fi

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
\let\oldpagestyle\pagestyle
\def\sinolPageStyle{fancy}
\renewcommand{\pagestyle}[1]{%
  \gdef\sinolPageStyle{#1}%
  \oldpagestyle{#1}
}

\newcommand{\signature}[1]{%
  \def\sinolSignature{#1}%
  \infoutput{[signature][#1]}%
  \global\signaturedefedtrue
}

\newcommand{\history}[3]{%
  \edef\sinolHistory{\noindent $\bullet$\ v.\,#3: #1, #2\par\sinolHistory}%
  \infoutput{[history][#1][#2][#3]}%
  \gdef\sinolDocVersion{#3}%
  \DocVersiondefedtrue%
}

\newcommand{\uses}[1]{%
  \infoutput{[uses][#1]}%
}

\renewcommand{\date}[1]{%
  \def\sinolDate{#1}%
  \global\datedefedtrue
}

\newcommand{\etap}[1]{%
  \def\sinolEtap{#1}%
  \global\etapdefedtrue
}

\renewcommand{\day}[1]{%
  \def\sinolDay{#1}%
  \global\daydefedtrue
}

\newcommand{\RAM}[1]{
  \def\sinolRAM{#1}%
  \global\RAMdefedtrue
}

\newcommand{\Time}[1]{
  \def\sinolTime{#1\,s}%
  \global\timedefedtrue
}

\newcommand{\Country}[1]{
  \def\sinolCountry{#1}%
  \global\Countrydefedtrue
}

\newcommand{\infile}{{\ttfamily XXX.IN}}
\newcommand{\outfile}{{\ttfamily XXX.IN}}

\def\sinolContestLogo{OIlogo}
\def\sinolLang{polish}

\def\sinolSolNameC{.c}
\def\sinolSolNameCPP{.cpp}
\def\sinolSolNamePAS{.pas}

\def\sinolTitlePomysl{Pomys³}
\def\sinolTitleZadanie{Zadanie}
\def\sinolTitleRecenzja{Recenzja}
\def\sinolTitleSpecyfikacja{Specyfikacja}
\def\sinolTitleOpracowanie{Opracowanie}
\def\sinolTitleWeryfikacja{Weryfikacja}
\def\sinolTitleCountry{Country}

\def\sinolSNamePrzyklad{Przyk³ad}
\def\sinolSNameZadanie{Zadanie}
\def\sinolSNameWejscie{Wej¶cie}
\def\sinolSNameWyjscie{Wyj¶cie}
\def\sinolSNameRozwiazanieWzorcowe{Rozwi±zanie wzorcowe}
\def\sinolSNameTesty{Testy}
\def\sinolSNameUwagi{Uwagi}
\def\sinolSNameHistory{HISTORIA}

\def\sinolEtapText{Etap}
\def\sinolDayText{Dzieñ}
\def\sinolSourceText{Plik ¼ród³owy}
\def\sinolRAMText{Dostêpna pamiêæ}
\def\sinolTimeText{Maksymalny czas dzia³ania}

\newcommand{\iomode}[1]{
    \def\sinolIOmode{#1}
    \ifeq{#1}{files}{
        \gdef\sinolExampleInputText{Dla pliku wej¶ciowego \infile:}
        \gdef\sinolExampleOutputText{poprawnym wynikiem jest plik wyj¶ciowy \outfile{}:}    
    }
    \ifeq{#1}{stdin}{
        \gdef\sinolExampleInputText{Dla danych wej¶ciowych:}
        \gdef\sinolExampleOutputText{poprawnym wynikiem jest:}    
    }    
    \ifeq{#1}{outputonly}{
        \gdef\sinolExampleInputText{Dla danych wej¶ciowych:}
        \gdef\sinolExampleOutputText{poprawnym wynikiem jest:}    
    }    
    \ifeq{#1}{interactive}{
        \gdef\sinolExampleInputText{Dla danych wej¶ciowych:}
        \gdef\sinolExampleOutputText{poprawnym wynikiem jest:}    
    }    
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Angielska wersja napisów                                % 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\DeclareOption{en}{%
\def\sinolLang{english}
%\selectlanguage{english}

\def\sinolTitlePomysl{Idea}
\def\sinolTitleZadanie{Task}
\def\sinolTitleRecenzja{Review}
\def\sinolTitleSpecyfikacja{Specification}
\def\sinolTitleOpracowanie{Analysis}
\def\sinolTitleWeryfikacja{Verification}

\def\sinolSNamePrzyklad{Example}
\def\sinolSNameZadanie{Task}
\def\sinolSNameWejscie{Input}
\def\sinolSNameWyjscie{Output}
\def\sinolSNameUwagi{Comments}
\def\sinolSNameRozwiazanieWzorcowe{Model solution}
\def\sinolSNameTesty{Tests}
\def\sinolSNameHistory{HISTORY}

\def\sinolEtapText{Stage}
\def\sinolDayText{Day}
\def\sinolSourceText{Source file}
\def\sinolRAMText{Available memory}
\def\sinolTimeText{Maximum running time}

\renewcommand{\iomode}[1]{
    \def\sinolIOmode{#1}
    \ifeq{#1}{files}{
        \gdef\sinolExampleInputText{For the input file \infile:}
        \gdef\sinolExampleOutputText{the correct result is the output file \outfile{}:}    
    }
    \ifeq{#1}{stdin}{
        \gdef\sinolExampleInputText{For the input data:}
        \gdef\sinolExampleOutputText{the correct result is:}
    }    
    \ifeq{#1}{outputonly}{
        \gdef\sinolExampleInputText{For the input data:}
        \gdef\sinolExampleOutputText{the correct result is:}
    }    
    \ifeq{#1}{interactive}{
        \gdef\sinolExampleInputText{For the input data:}
        \gdef\sinolExampleOutputText{the correct result is:}
    }    
}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Czeska wersja napisów                                   % 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\DeclareOption{cz}{%
\def\sinolLang{czech}
%\selectlanguage{czech}

\def\sinolTitleZadanie{\'Uloha}
\def\sinolSNamePrzyklad{P\v{r}{\'\i}klad}
\def\sinolSNameZadanie{\'Uloha}
\def\sinolSNameWejscie{Vstup}
\def\sinolSNameWyjscie{V\'ystup}
\def\sinolSNameUwagi{???}
\renewcommand{\iomode}[1]{
    \def\sinolIOmode{#1}
    \ifeq{#1}{files}{
        \gdef\sinolExampleInputText{??? \infile:}
        \gdef\sinolExampleOutputText{??? \outfile{}:}    
    }
    \ifeq{#1}{stdin}{
        \gdef\sinolExampleInputText{Pro vstupn{\'\i} data:}
        \gdef\sinolExampleOutputText{je spr\'avn\'y v\'ystup:}
    }    
    \ifeq{#1}{outputonly}{
        \gdef\sinolExampleInputText{Pro vstupn{\'\i} data:}
        \gdef\sinolExampleOutputText{je spr\'avn\'y v\'ystup:}
    }    
    \ifeq{#1}{interactive}{
        \gdef\sinolExampleInputText{Pro vstupn{\'\i} data:}
        \gdef\sinolExampleOutputText{je spr\'avn\'y v\'ystup:}
    }    
}
\def\sinolEtapText{???}
\def\sinolDayText{Den}
\def\sinolSourceText{Zdrojov\'y soubor}
\def\sinolRAMText{Dostupn\'a pam\v{e}t'}
\def\sinolTimeText{Maxim\'aln{\'\i} doba b\v{e}hu}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Horwacka wersja napisów                                 % 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\DeclareOption{hr}{%
\def\sinolLang{croatian}
%\selectlanguage{croatian}

\def\sinolTitleZadanie{Zadatak}
\def\sinolSNamePrzyklad{Primjer}
\def\sinolSNameZadanie{Zadatak}
\def\sinolSNameWejscie{Ulazni podaci}
\def\sinolSNameWyjscie{Izlazni podaci}
\def\sinolSNameUwagi{???}
\renewcommand{\iomode}[1]{
    \def\sinolIOmode{#1}
    \ifeq{#1}{files}{
        \gdef\sinolExampleInputText{??? \infile:}
        \gdef\sinolExampleOutputText{??? \outfile{}:}    
    }
    \ifeq{#1}{stdin}{
        \gdef\sinolExampleInputText{Za ulazne podatke:}
        \gdef\sinolExampleOutputText{ispravno rje\v{s}enje glasi:}
    }    
    \ifeq{#1}{outputonly}{
        \gdef\sinolExampleInputText{Za ulazne podatke:}
        \gdef\sinolExampleOutputText{ispravno rje\v{s}enje glasi:}
    }    
    \ifeq{#1}{interactive}{
        \gdef\sinolExampleInputText{Za ulazne podatke:}
        \gdef\sinolExampleOutputText{ispravno rje\v{s}enje glasi:}
    }    
}
\def\sinolEtapText{???}
\def\sinolDayText{Dan}
\def\sinolSourceText{Izvorni kod}
\def\sinolRAMText{Memorijsko ograni\v{c}enje}
\def\sinolTimeText{Vremensko ograni\v{c}enje}
}

\iomode{files}

\newcommand{\iffileexists}[3]{%
  \immediate\openin\tmpfile #1\par
  \ifeof\tmpfile
    \immediate\closein\tmpfile
    #3
  \else
    \immediate\closein\tmpfile
    #2
  \fi
}

\AtBeginDocument{%
  \immediate\openout\inffile \jobname.inf
  \immediate\openout\errfile \jobname.err
}

\AtEndDocument{%
  \ifsinolerrors
    \immediate\write16{SINOL: znaleziono bledy (zob. \jobname.err) !}
  \fi
  \ifsinolshortages
    \immediate\write16{SINOL: znaleziono niedoprecyzowania (wystepuje '[[[...]]]')}
  \fi
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Niemiecka wersja napisów                                % 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\DeclareOption{de}{%
\def\sinolLang{german}
%\selectlanguage{german}

\def\sinolTitlePomysl{Idea}
\def\sinolTitleZadanie{Aufgabe}
\def\sinolTitleRecenzja{Review}
\def\sinolTitleSpecyfikacja{Specification}
\def\sinolTitleOpracowanie{Analysis}
\def\sinolTitleWeryfikacja{Verification}

\def\sinolSNamePrzyklad{Beispiel}
\def\sinolSNameZadanie{Aufgabe}
\def\sinolSNameWejscie{Eingabe}
\def\sinolSNameWyjscie{Ausgabe}
\def\sinolSNameUwagi{Comments}
\def\sinolSNameRozwiazanieWzorcowe{Model solution}
\def\sinolSNameTesty{Tests}
\def\sinolSNameHistory{HISTORY}

\def\sinolEtapText{Stage}
\def\sinolDayText{Tag}
\def\sinolSourceText{Quelldatei}
\def\sinolRAMText{Speicherlimit}
\def\sinolTimeText{Maximale Laufzeit}

\renewcommand{\iomode}[1]{
    \def\sinolIOmode{#1}
    \ifeq{#1}{files}{
        \gdef\sinolExampleInputText{For the input file \infile:}
        \gdef\sinolExampleOutputText{the correct result is the output file \outfile{}:}    
    }
    \ifeq{#1}{stdin}{
        \gdef\sinolExampleInputText{F\"ur die Eingabe:}
        \gdef\sinolExampleOutputText{lautet das richtige Ergebnis:}
    }    
    \ifeq{#1}{outputonly}{
        \gdef\sinolExampleInputText{F\"ur die Eingabe:}
        \gdef\sinolExampleOutputText{lautet das richtige Ergebnis:}
    }    
    \ifeq{#1}{interactive}{
        \gdef\sinolExampleInputText{F\"ur die Eingabe:}
        \gdef\sinolExampleOutputText{lautet das richtige Ergebnis:}
    }    
}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\DeclareOption{pom}{%
  \def\sinolcat{pom}
  \def\xsinolcat{\sinolTitlePomysl}
  \newcommand{\source}[1]{%
    \def\sinolSource{#1}%
    \infoutput{[source][#1]}%
  }
  \renewcommand{\author}[1]{%
    \def\sinolAuthor{#1}%
    \infoutput{[author][#1]}%
  }
  \renewcommand{\title}[1]{%
    \def\sinolTitle{#1}%
    \infoutput{[title][#1]}%
  }
  \newcommand{\makemetric}{%
    {
      \footnotesize
      {\noindent\bfseries \sinolSourceText:}
        \ifundef{sinolSource}{\?{brak}}{\sinolSource}\par
      {\noindent\bfseries \sinolSNameHistory:}\par
      \sinolHistory
    }
  }
  \renewcommand{\concludedecls}{%
    \edef\sinolIdSignature{\sinolSignature}%
  }%
}

\DeclareOption{spe}{%
  \def\sinolcat{spe}
  \def\xsinolcat{\sinolTitleSpecyfikacja}
  \renewcommand{\title}[1]{%
    \def\sinolTitle{#1}%
    \infoutput{[title][#1]}%
  }
  \newcommand{\id}[1]{%
    \edef\ID{#1}%
    \infoutput{[id][#1]}%
  }
  \newcommand{\makemetric}{%
    {
      \footnotesize
      {\noindent\bfseries \sinolSNameHistory:}\par
      \sinolHistory
    }
  }
  \renewcommand{\concludedecls}{%
    \edef\sinolIdSignature{\sinolSignature}%
  }%
}

\newcommand\includefile[1]{
\vspace{-0.7em}
\verbatiminput{#1}
}


\def\sinolCatNameZad{zad}
\DeclareOption{zad}{%
  \def\sinolcat{zad}
  \def\xsinolcat{\sinolTitleZadanie}
  \renewcommand{\title}[1]{%
    \def\sinolTitle{#1}%
    \infoutput{[title][#1]}%
  }
  \newcommand{\id}[1]{%
    \edef\ID{#1}%
    \infoutput{[id][#1]}%
  }

  \newcommand{\exampleinputimg}[1]{%
    \edef\exampleInImg{#1}%
  }

  \newcommand{\exampleoutputimg}[1]{%
    \edef\exampleOutImg{#1}%
  }

  \newcommand{\exampleimg}[1]{%
    \edef\exampleImg{#1}%
  }

  \newcommand{\makemetric}{%
    {
      \footnotesize
      {\noindent\bfseries \sinolSNameHistory:}\par
      \sinolHistory
    }
  }

  \newcommand{\exampleinput}{%
      \iffileexists{\sinolTestIn/\ID0.in}{%
          \includefile{\sinolTestIn/\ID0.in}
      }{
       \iffileexists{\ID0.in}{%
          \includefile{\ID0.in}
       }{
         \smallskip
         \?{brak pliku {\ttfamily\ID0.in}}\par
         \erroutput{brak pliku '\ID0.in'}
         \smallskip
       }
      }
  }

  \newcommand{\exampleoutput}{%
    \iffileexists{\sinolTestOut/\ID0.out}{%
      \includefile{\sinolTestOut/\ID0.out}
    }{
      \iffileexists{\ID0.out}{%
         \includefile{\ID0.out}
      }{    
       \smallskip
       \?{brak pliku {\ttfamily\ID0.out}}\par
       \erroutput{brak pliku '\ID0.out'}
       \smallskip
      }
    }
  }

  \def\sinolTestIn{.}
  
  \def\sinolTestOut{.}
  
  \def\@exampleputtogetherh#1#2{\twocol{#1}{#2}}

  \def\@exampleputtogetherv#1#2{#1 #2}

  \newcommand{\makestandardexampleinput}{%
    \sinolExampleInputText
    \ifundef{exampleInImg}{%
      \exampleinput
    }{
      \@exampleputtogetherimg{\exampleinput}{\plainimg{\exampleInImg}}
    }
  }

  \newcommand{\makestandardexampleoutput}{%
    \sinolExampleOutputText
    \ifundef{exampleOutImg}{%
      \exampleoutput
    }{
      \@exampleputtogetherimg{\exampleoutput}{\plainimg{\exampleOutImg}}
    }
  }

  \newcommand{\loadtestdir}{
    \openin\tmpfile testdir.inp
    \ifeof\tmpfile
% TW, zazwyczaj ten plik nie jest stosowany, wiec komunikat o bledzie nie jest 
%     konieczny
%      \write16{SINOL: brak pliku 'testdir.inp'}
    \else
      \read\tmpfile to\sinolTestIn
      \ifeof\tmpfile
        \write16{SINOL: plik 'testdir.inp' skonczyl sie zbyt wczesnie}
      \else
        \read\tmpfile to\sinolTestOut
      \fi
    \fi
    \closein\tmpfile
  }

  \newcommand{\@makestandardexampletext}{%
    \@exampleputtogethertext{%
      \makestandardexampleinput
    }{%
      \makestandardexampleoutput
    }
  }

  \newcommand{\@makeexample}{%
    \loadtestdir   
    \section{\sinolSNamePrzyklad}
    \ifundef{exampleImg}{%
      \@makestandardexampletext
    }{%
      \@exampleputtogetherimg{%
        \@makestandardexampletext
      }{
        \plainimg{\exampleImg}
      }
    }
  }


  \newcommand{\makestandardexample}{%
    \let\@exampleputtogetherimg=\@exampleputtogetherh
    \let\@exampleputtogethertext=\@exampleputtogetherv
    \@makeexample
  }

  \newcommand{\makecompactexample}{%
    \def\@exampleputtogetherimg##1##2{%
      \@exampleputtogetherv{##1}{%
        \begin{center}
          ##2
        \end{center}
      }
    }
    \let\@exampleputtogethertext=\@exampleputtogetherh
    \@makeexample
  }

  \renewcommand{\concludedecls}{%
    \ifundef{ID}{%
      \erroutput{brak 3-literowego identyfikatora (klauzula \string\id)}%
      \def\ID{XXX}%
    }{}%
    \def\infile{{\ttfamily \lcase{\ID}.in}}%
    \def\outfile{{\ttfamily \lcase{\ID}.out}}%
    \ifundef{sinolTitle}{%
      \erroutput{brak tytulu (klauzula \string\title)}%
      \def\sinolTitle{\?{brak tytu^^b3u}}%
    }{}%
    \ifzawodnik%
      \def\sinolIdSignature{\ucase{\ID}}%
    \else%
      \def\sinolIdSignature{\ID/\sinolSignature}%
    \fi%
    \let\oldsection\section%
    \renewcommand{\section}[1]{%
      \def\@tmparg{##1}%
      \oldsection*{##1}%
      \ifnum\sinolSectionNumber=0%
        \ifeq{\@tmparg}{\sinolSNameZadanie}{%
          \sinolSectionNumber=1%
        }%
      \fi%
      \ifcase\sinolSectionNumber%
        \ifneq{\@tmparg}{\sinolSNamePrzyklad}{%
          \erroutputWrongSection{\@tmparg}{\sinolSNamePrzyklad}%
        }%
      \or%
        \ifneq{\@tmparg}{\sinolSNameZadanie}{%
          \erroutputWrongSection{##1}{\sinolSNameZadanie}%
        }%
      \or%
        \ifneq{\@tmparg}{\sinolSNameWejscie}{%
          \erroutputWrongSection{##1}{\sinolSNameWejscie}%
        }%
      \or%
        \ifneq{\@tmparg}{\sinolSNameWyjscie}{%
          \erroutputWrongSection{##1}{\sinolSNameWyjscie}%
        }%
      \or%
        \ifneq{\@tmparg}{\sinolSNamePrzyklad}{%
          \erroutputWrongSection{\@tmparg}{\sinolSNamePrzyklad}%
        }%
      \else%
        \ifneq{\@tmparg}{\sinolSNameUwagi}{%
          \erroutput{nadmiarowy rozdzial '##1'}%
        }%
      \fi%
      \advance\sinolSectionNumber+1%
    }%
  }%

  \renewcommand{\concludetext}{
    \ifnum\sinolSectionNumber=5\else
      \erroutput{niewlasciwa liczba rozdzialow}
    \fi
    \ifeq{\cstyle}{appendix}{\showComments}
  }
}

\DeclareOption{rec}{%
  \def\sinolcat{rec}
  \def\xsinolcat{\sinolTitleRecenzja}
  \renewcommand{\title}[1]{%
    \def\sinolTitle{#1}%
    \infoutput{[title][#1]}%
  }
  \newcommand{\id}[1]{%
    \edef\ID{#1}%
    \infoutput{[id][#1]}%
  }
  \newcommand{\makemetric}{%
    {
      \footnotesize
      {\noindent\bfseries \sinolSNameHistory:}\par
      \sinolHistory
    }
  }
  \renewcommand{\title}[1]{%
    \def\sinolTitle{#1}%
    \infoutput{[title][#1]}%
  }

  \renewcommand{\concludedecls}{%
    \ifundef{ID}{%
      \def\ID{XXX}%
    }{}%
    \ifundef{sinolTitle}{%
      \def\sinolTitle{\?{tytu^^b3 zostanie wygenerowany}}%
    }{}%
    \def\sinolIdSignature{\ID/\sinolSignature}%
  }%
}

\DeclareOption{opr}{%
  \def\sinolcat{opr}
  \def\xsinolcat{\sinolTitleOpracowanie}
  \renewcommand{\title}[1]{%
    \def\sinolTitle{#1}%
    \infoutput{[title][#1]}%
  }
  \newcommand{\id}[1]{%
    \edef\ID{#1}%
    \infoutput{[id][#1]}%
  }
  \newcommand{\makemetric}{%
    {
      \footnotesize
      {\noindent\bfseries \sinolSNameHistory:}\par
      \sinolHistory
    }
  }
  \renewcommand{\title}[1]{%
    \def\sinolTitle{#1}%
    \infoutput{[title][#1]}%
  }

  \renewcommand{\concludedecls}{%
    \ifundef{ID}{%
      \def\ID{XXX}%
    }{}%
    \def\infile{{\ttfamily \lcase{\ID}.in}}%
    \def\outfile{{\ttfamily \lcase{\ID}.out}}%
    \ifundef{sinolTitle}{%
      \def\sinolTitle{\?{tytu^^b3 zostanie wygenerowany}}%
    }{}%
    \def\sinolIdSignature{\ucase{\ID}}%
    %
    \newif\ifsectionPresentTesty \sectionPresentTestyfalse%
    \newif\ifsectionPresentRozwiazanieWzorcowe%
         \sectionPresentRozwiazanieWzorcowefalse%
    %
    \let\oldsection\section%
    \renewcommand{\section}[1]{%
      \def\@tmparg{##1}%
      \oldsection{##1}%
      \ifx\@tmparg\sinolSNameTesty%
        \ifsectionPresentTesty%
          \erroutput{powtorzony rozdzial '\@tmparg'}%
        \else%
          \global\sectionPresentTestytrue%
        \fi%
      \fi%
      \ifx\@tmparg\sinolSNameRozwiazanieWzorcowe%
        \ifsectionPresentRozwiazanieWzorcowe%
          \erroutput{powtorzony rozdzial '\@tmparg'}%
        \else%
          \global\sectionPresentRozwiazanieWzorcowetrue%
        \fi%
      \fi%
    }%
  }%

  \renewcommand{\concludetext}{
    \ifidealSolutionPresent\else
      \erroutput{brak odniesienia do rozwiazania optymalnego}
    \fi
    \ifsectionPresentTesty\else
      \erroutput{brak rozdzialu '\sinolSNameTesty'}
    \fi
    \ifsectionPresentRozwiazanieWzorcowe\else
      \erroutput{brak rozdzialu '\sinolSNameRozwiazanieWzorcowe'}
    \fi
  }

  \newif\ifidealSolutionPresent \idealSolutionPresentfalse

  \newcommand{\solution}[1]{%
    \infoutput{[solution][##1]}%
    \infoutput{[uses][prog/##1]}%
    {\ttfamily prog/\ID#1}%
    \def\@tmparg{#1}
    \ifx\@tmparg\sinolSolNameC
      \idealSolutionPresenttrue
    \fi
    \ifx\@tmparg\sinolSolNameCPP
      \idealSolutionPresenttrue
    \fi
    \ifx\@tmparg\sinolSolNamePAS
      \idealSolutionPresenttrue
    \fi
  }

  \newenvironment{tests}{%
    \newcommand{\test}[3]{%
      \item {\ttfamily \ID##1.IN} ($##2$ sek.) ##3\par
      \infoutput{[test][##1]}
      \infoutput{[uses][in/##1.in]}
      \infoutput{[uses][out/##1.in]}
    }
    \begin{itemize}
  }{%
    \end{itemize}
  }
}


\DeclareOption{wer}{%
  \def\sinolcat{wer}
  \def\xsinolcat{\sinolTitleWeryfikacja}
  \renewcommand{\title}[1]{%
    \def\sinolTitle{#1}%
    \infoutput{[title][#1]}%
  }
  \newcommand{\id}[1]{%
    \edef\ID{#1}%
    \infoutput{[id][#1]}%
  }
  \newcommand{\makemetric}{%
    {
      \footnotesize
      {\noindent\bfseries \sinolSNameHistory:}\par
      \sinolHistory
    }
  }
  \renewcommand{\title}[1]{%
    \def\sinolTitle{#1}%
    \infoutput{[title][#1]}%
  }

  \renewcommand{\concludedecls}{%
    \ifundef{ID}{%
      \def\ID{XXX}%
    }{}%
    \ifundef{sinolTitle}{%
      \def\sinolTitle{\?{tytu^^b3 zostanie wygenerowany}}%
    }{}%
    \def\sinolIdSignature{\ID/\sinolSignature}%
  }%
}

\DeclareOption{zawodnik}{%
  \global\zawodniktrue
  \ifx\sinolcat\sinolCatNameZad
    \global\metricfalse
    \renewcommand{\?}[1]{%
      [[[#1]]]%
      \errmessage{SINOL: przy opcji 'zawodnik' nie wolno uzywac %
        '\string\?\string{...\string}'}
    }
  \else
    \errmessage{SINOL: opcja 'zawodnik' moze wystepowac tylko po opcji 'zad'}
  \fi
}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax
\PassOptionsToClass{a4paper}{article}
\LoadClass{article}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% rozmiar papieru
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\setlength{\textwidth}{180mm}
\setlength{\textheight}{257mm}
\setlength{\oddsidemargin}{0pt}
\setlength{\topmargin}{0pt}
\setlength{\hoffset}{-10mm} % this means 1in-15mm
\setlength{\voffset}{-20mm} % this means 1in-15mm
\setlength{\topmargin}{0pt}
%% w przypadku stylu fancy, trzeba wy³±czyæ rysowanie linii w nag³ówku
\headrulewidth 0pt
%\oldtitle{}
%\oldauthor{}
%\date{}

\newenvironment{text}{%
  \expandafter\selectlanguage\expandafter{\sinolLang}%
  \ifsignaturedefed\else%
    \erroutput{brak sygnatury}%
  \fi%
  %% definiowanie stopek dla stylu fancy
  \ifeq{\sinolPageStyle}{fancy}{%
    \lfoot{\ifDocVersiondefed v.\,\sinolDocVersion \fi}%
    \cfoot{\thepage/\pageref{koniec}}%
    \rfoot{\sinolTitle}%
  }%
  \concludedecls%
  {%
    %\sffamily\bfseries
    %\LARGE
    %\leftline{\xsinolcat: \sinolIdSignature}
    %\leftline{\sinolTitle}
    \leftline{%
      \begin{minipage}[t]{0.4\textwidth}
        \sffamily\bfseries%
        \LARGE%
        \xsinolcat: \sinolIdSignature\\
        \sinolTitle
      \end{minipage}
      \begin{minipage}[t]{0.2\textwidth}
        \sffamily\bfseries%
        \large%
        \center
        \ifCountrydefed 
          %\sinolTitleCountry: 
          \sinolCountry 
        \fi
      \end{minipage}
    }%
  }%
  \ifzawodnik
    \hbox to\hsize{\hfil\LOGO}\smallskip
  \else
    \medskip
  \fi
  \hrule
  \smallskip
  \ifmetric
    \makemetric
    \smallskip
    \hrule
  \fi
  \ifzawodnik
    \smallskip
    \hbox to\hsize{%
      {\bf
        \def\@tempempty{}%
        %% Etap pokazuje siê tylko gdy jest niepusty
        \ifetapdefed%
          \ifx\sinolEtap\@tempempty%
          \else%
            \sinolEtapText\ %
            \sinolEtap.
          \fi%
        \else\?{brak}\erroutput{brak etapu}\fi%
        %% dzieñ pokazuje siê tylko gdy jest niepusty
        \ifdaydefed%
          \ifx\sinolDay\@tempempty%
          \else
            \sinolDayText\ 
            \sinolDay.
          \fi%
        \else\?{brak}\erroutput{brak dnia}\fi%
        %% Plik ¼ród³owy -- pokazuje sie, gdy 
        %% sinolIOmode <> outputonly
        %\ifneq{\sinolIOmode}{outputonly}{
        %  \hskip 7pt
        %  \sinolSourceText\
        %  {\tt \ID.*}%
        %}%
      }%
    %}%
    %\smallskip
    %\hbox to\hsize{%
      \bf
      %% Dostêpna pamiêæ -- pokazuje sie tylko gdy
      %% nie jest pusta i jest zdefiniowana
      \ifRAMdefed%
        \ifx\sinolRAM\@tempempty%
        \else%
          \sinolRAMText:\
          \sinolRAM\,MB. 
        \fi%
      \else\fi%
      %% Maksymalny czas dzia³ania -- pokazuje siê tylko gdy nie 
      %% jest pusty i jest zdefiniowany.
      \iftimedefed%
        \ifx\sinolTime\@tempempty%
        \else%
          \sinolTimeText:\
          \sinolTime.
        \fi%
      \else\fi%
      \hfill
      \ifdatedefed{\it\sinolDate}\else\?{brak daty}\erroutput{brak daty}\fi
    }
    \bigskip
  \else
    \vskip1.5pt
    {\tiny\rightline{%
      dokument systemu SINOL \sinolVersion
    }}
    \smallskip
  \fi
  \noindent
  \ignorespacesafterend
}{%
  %\smallskip
  %\finalclause
  \concludetext
  \closeout\inffile
  \closeout\errfile
  \label{koniec}%
}
