FROM sjkillen/lean3c
LABEL maintainer="sjkillen@ualberta.ca"

RUN apt-get -qq update
RUN apt-get -qq install sudo

ARG USERNAME=prover
ARG USER_UID=1000
ARG USER_GID=$USER_UID

# Copied from https://code.visualstudio.com/docs/remote/containers-advanced#_adding-a-nonroot-user-to-your-dev-container

# Create the user
RUN groupadd --gid $USER_GID $USERNAME \
    && useradd --uid $USER_UID --gid $USER_GID -m $USERNAME --shell /bin/bash \
    #
    # [Optional] Add sudo support. Omit if you don't need to install software after connecting.
    && echo $USERNAME ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/$USERNAME \
    && chmod 0440 /etc/sudoers.d/$USERNAME


USER $USERNAME

ENTRYPOINT ["bash"]
