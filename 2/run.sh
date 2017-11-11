for file in *correct*.in
do
    echo $file 
    ./2.exe < $file > ${file%.*}.out
done