cd ~/plfa && git submodule update --init --recursive

mkdir  ~/.agda
cp ~/plfa/data/dotagda/* ~/.agda

agda-mode setup
agda-mode compile

cat ~/plfa/.devcontainer/.emacs >> ~/.emacs