for %%f in (*.dot) do (
	dot.exe -Tpng %%~nf.dot -o %%~nf.png
)

