# Pass FNAME name with "FNAME=xxx" command line argument

makeDirs= mkdir -p out log csrc no_backup no_backup/tmp

INCDIR = posit/

vcsBaseCommand= vcs -full64 -sverilog -timescale=1ns/10ps +notimingchecks +lint=PCWM \
								-notice -Mdir=csrc +lint=TFIPC-L \
								+define+VERIFICATION

vcsFiles= -l ./log/compile \
-o ./out/simv +incdir+$(INCDIR) \
 $(FNAME) 

vcsCompileCommand =  $(vcsBaseCommand) $(vcsFiles) 

# Pass FNAME name with "FNAME=xxx" command line argument
lint:
	$(makeDirs) 
	$(vcsCompileCommand)

#clean:
#	\rm -rf simv* *.log *.vpd *.dump csrc *.sim *.mra *.log ucli.key session* *.db vcs.key 

clean:
	\rm -rf simv* *.log *.vpd *.dump csrc *.sim *.mra *.log *.logv *.cmd ucli.key session* *.db vcs.key out/simv* tmp DVEfiles vc_hdrs.h
